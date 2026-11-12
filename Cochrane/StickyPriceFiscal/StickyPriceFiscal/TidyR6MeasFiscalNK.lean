/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.PolicyRulesMeasure
import StickyPriceFiscal.Links

/-!
# The sticky-price fiscal model of §§5.1–5.2 in a probability model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, eqs. (5.1)–(5.4),
pp. 117–119, §5.1.2, eqs. (5.11)–(5.16), pp. 120–125, and §5.2, eqs. (5.17)–(5.21),
pp. 127–129, restated with **measure-theoretic expectations**: an
`ExpectationsMeasure.MeasExpectationSystem` (Mathlib's `MeasureTheory.condExp` on a filtered
probability space), every equation an almost-everywhere equality, adapted meaning
`MeasureTheory.StronglyAdapted`, bounded meaning a uniform essential bound. The core
modules `NKModel`, `FiscalNK`, `LongTermDebt` prove the same claims for the abstract
`ExpectationSystem`, which cannot carry nondegenerate infinite-horizon uncertainty.

The roots are those of (5.6): `λ_S = λ₁⁻¹ ∈ (0, 1)`, `λ_U = λ₂⁻¹ > 1` (`roots_nk`), for every
`σ, κ, β > 0` (no `β < 1` needed). The `(x, π)` algebra is `PolicyRulesMeasure.blk_pt` with the
no-rule parameters `nkP`.

## Main results

* (5.4) `mpc_forward`: `π_t = ∑ βᵏ κ E_t x_{t+k}` a.e. (genuine series) for bounded `x, π`,
  `0 < β < 1`; (5.3) `mis_iterate`, `mis_iterate_limit`.
* `mnk_props`: in every bounded adapted solution of (5.1)–(5.2), `f = x − gπ` solves the
  forward equation `f_t = λ_U⁻¹ E_t f_{t+1} − (σ/λ_U) i_t` and `E_t π_{t+1} = λ_S π_t − (κ/β) f_t`.
* The fiscal model (5.15)–(5.16) in general form `MEqm` (flow `ρ v_{t+1} = v_t − π_{t+1} −
  e_{t+1}`, date-0 flow from `b₀`), `MTVC`:
  **`meqm_unique_tvc`** (`0 < ρ ≤ 1`: at most one equilibrium satisfying the transversality
  condition, a.e. at every date), **`meqm_unique`** (`0 < ρ < 1`, bounded), **`meqm_exists`**
  (`0 < ρ < 1`: an equilibrium exists for every bounded adapted `i`, `e` and bounded
  `𝓕₀`-measurable `b₀`), **`meqm_determinate`**.
* `rho_one_not_unique` (E20/E32 in a probability model): at `ρ = 1` every equilibrium has a
  distinct bounded companion with the same data.
* (5.11)–(5.13): `mvaluation` (`v_t = ∑ ρᵏ E_t(π_{t+1+k} + e_{t+1+k})` a.e.), `mflow_innov`
  (unexpected inflation `ΔE_{t+1}π_{t+1} = −ΔE_{t+1}e_{t+1} − ρ ΔE_{t+1}v_{t+1}`).
* One-period debt (5.16): `MFTPLNK`, `mftplnk_iff` (the book's model is the general one with
  forcing `s̃_{t+1} − i_t`), `eShort_adaptedM`, `eShort_bddM`, `mftplnk_determinate`;
  long-term debt (5.17)–(5.21): `MLTD`, `mltd_eqm`, `mbond_price` (the bounded bond price is the
  forward solution), **`mltd_determinate`**, `meqm_congr`.
* §5.1.1, (5.5)–(5.7): **`mnk_characterization`** (all bounded equilibria of (5.1)–(5.2)) and
  `mnk_ma` (the moving-average form).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasFiscalNK

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRules PolicyRulesMeasure NKModel

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Roots and the `(x, π)` block -/

/-- Cochrane (2023), §5.1, p. 118: the new-Keynesian parameters as `PolicyRules.Params` with no
rules (`θ = 0`, `α = 0`). -/
def nkP (σ β κ : ℝ) : Params := { zeroParams with sigma := σ, kappa := κ, beta := β }

/-- Cochrane (2023), (5.6), p. 119: the stable root `λ_S = λ₁⁻¹`. -/
noncomputable def lS (σ β κ : ℝ) : ℝ := (lam1 σ β κ)⁻¹

/-- Cochrane (2023), (5.6), p. 119: the unstable root `λ_U = λ₂⁻¹`. -/
noncomputable def lU (σ β κ : ℝ) : ℝ := (lam2 σ β κ)⁻¹

/-- Cochrane (2023), (5.6), p. 119 and A1 §1.9, p. 574: for `σ, κ, β > 0`, `λ_U + λ_S = tr`,
`λ_U λ_S = det` of the no-rule block, `λ_U > 1` and `0 < λ_S < 1`. -/
theorem roots_nk {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    lU σ β κ + lS σ β κ = trB (nkP σ β κ) ∧ lU σ β κ * lS σ β κ = detB (nkP σ β κ) ∧
      1 < lU σ β κ ∧ 0 < lS σ β κ ∧ lS σ β κ < 1 := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hs := lam_sum σ β κ
  have hp := lam_prod ha hβ
  have hl1 : lam1 σ β κ ≠ 0 := by linarith
  refine ⟨?_, ?_, one_lt_inv₀ h2 |>.mpr h21, inv_pos.mpr (by linarith),
    inv_lt_one_of_one_lt₀ h1⟩
  · rw [trB_eq, lU, lS]
    simp only [nkP, zeroParams]
    field_simp
    nlinarith
  · rw [detB_eq (by simpa [nkP] using hβ.ne'), lU, lS]
    simp only [nkP, zeroParams]
    field_simp
    nlinarith

/-- Cochrane (2023), eqs. (5.1)–(5.2), p. 118, in a probability model (a.e.). -/
def MNK (σ β κ : ℝ) (i x p : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • (i t - S.E t (p (t + 1)))) ∧
  (∀ t, p t =ᵐ[S.μ] β • S.E t (p (t + 1)) + κ • x t)

/-- Cochrane (2023), §5.1, A1 §1.7, pp. 569–570, in a probability model: in every bounded adapted
solution of (5.1)–(5.2) with bounded adapted `i`, `f = x − gπ` (`g = (1 − βλ_S)/κ`) solves
`f_t = λ_U⁻¹ E_t f_{t+1} − (σ/λ_U) i_t`, and `E_t π_{t+1} = λ_S π_t − (κ/β) f_t` a.e. -/
theorem mnk_props {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i x p : ℕ → Ω → ℝ}
    (h : MNK S σ β κ i x p) (hxa : StronglyAdapted S.𝓕 x) (hpa : StronglyAdapted S.𝓕 p)
    (hxb : S.BddProc x) (hpb : S.BddProc p) :
    S.Solves (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t)
        (fwd (gainOf (nkP σ β κ) (lS σ β κ)) x p) ∧
      ∀ t, S.E t (p (t + 1)) =ᵐ[S.μ] lS σ β κ • p t -
        (κ / β) • fwd (gainOf (nkP σ β κ) (lS σ β κ)) x p t := by
  obtain ⟨hsum, hprod, hU, -, -⟩ := roots_nk hσ hκ hβ
  have hβ' : (nkP σ β κ).beta ≠ 0 := by simpa [nkP] using hβ.ne'
  have hκ' : (nkP σ β κ).kappa ≠ 0 := by simpa [nkP] using hκ.ne'
  have hU0 : lU σ β κ ≠ 0 := by linarith
  set G := gainOf (nkP σ β κ) (lS σ β κ)
  have key : ∀ t, ∀ᵐ ω ∂S.μ, S.E t (x (t + 1)) ω - G * S.E t (p (t + 1)) ω =
      lU σ β κ * (x t ω - G * p t ω) + σ * i t ω ∧
      S.E t (p (t + 1)) ω = lS σ β κ * p t ω - κ / β * (x t ω - G * p t ω) := by
    intro t
    filter_upwards [h.1 t, h.2 t] with ω e64 e65
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at e64 e65
    have := blk_pt (P := nkP σ β κ) hβ' hκ' hsum hprod (X := x t ω) (Pp := p t ω)
      (U := i t ω) (EX := S.E t (x (t + 1)) ω) (EP := S.E t (p (t + 1)) ω)
      (by simp only [nkP, zeroParams]; linarith) (by simp only [nkP]; linarith)
    exact this
  constructor
  · intro t
    filter_upwards [key t, E_sub_smul S (int_of S hxa hxb (t + 1)) (int_of S hpa hpb (t + 1)) G t]
      with ω k eE
    simp only [fwd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [eE, k.1]
    field_simp
    ring
  · intro t
    filter_upwards [key t] with ω k
    simp only [fwd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact k.2

/-! ### The fiscal model (5.15)–(5.16) -/

/-- Cochrane (2023), eqs. (5.15)–(5.16), p. 121, general form, in a probability model: the
new-Keynesian model, the flow `ρ v_{t+1} = v_t − π_{t+1} − e_{t+1}` and the date-0 flow
`ρ v_0 = b_0 − π_0 − e_0` (a.e.), with adapted `x, π, v` and bounded `x, π`. -/
def MEqm (σ β κ ρ : ℝ) (i e : ℕ → Ω → ℝ) (b0 : Ω → ℝ) (x p v : ℕ → Ω → ℝ) : Prop :=
  MNK S σ β κ i x p ∧ (∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t - p (t + 1) - e (t + 1)) ∧
  ρ • v 0 =ᵐ[S.μ] b0 - p 0 - e 0 ∧ StronglyAdapted S.𝓕 x ∧ StronglyAdapted S.𝓕 p ∧
  StronglyAdapted S.𝓕 v ∧ S.BddProc x ∧ S.BddProc p

/-- Cochrane (2023), pp. 121–122: the transversality condition `ρᵏ E_t v_{t+k} → 0` (a.e., at
every date), for an integrable value of debt. -/
def MTVC (ρ : ℝ) (v : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (v t) S.μ) ∧
    ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => ρ ^ k * S.E t (v (t + k)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 121 (tool): iterating `E_t d_{t+1} = λ d_t` gives
`E_t d_{t+k} = λᵏ d_t` a.e. -/
theorem E_iter {d : ℕ → Ω → ℝ} {l : ℝ} (hda : StronglyAdapted S.𝓕 d)
    (hdi : ∀ t, Integrable (d t) S.μ) (hd : ∀ t, S.E t (d (t + 1)) =ᵐ[S.μ] l • d t) (t : ℕ) :
    ∀ k, S.E t (d (t + k)) =ᵐ[S.μ] l ^ k • d t := by
  intro k
  induction k with
  | zero => simp [S.E_of_stronglyMeasurable (hda t) (hdi t)]
  | succ k ih =>
    rw [show t + (k + 1) = t + k + 1 by ring]
    filter_upwards [(S.E_tower (Nat.le_add_right t k) (d (t + k + 1))).symm,
      S.E_congr (hd (t + k)) t, S.E_smul l (d (t + k)) t, ih] with ω e1 e2 e3 e4
    rw [e1, e2, e3, Pi.smul_apply, e4]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), p. 121 (tool): the weight `c = λ_S/(1 − ρλ_S)` with `λ_S(1 + ρc) = c`. -/
theorem cW_eq {l ρ : ℝ} (h : 1 - ρ * l ≠ 0) :
    l * (1 + ρ * (l / (1 - ρ * l))) = l / (1 - ρ * l) := by
  have h2 : (1 - ρ * l) * (1 + ρ * (l / (1 - ρ * l))) = 1 := by
    field_simp
    ring
  rw [eq_div_iff h]
  calc l * (1 + ρ * (l / (1 - ρ * l))) * (1 - ρ * l) =
        l * ((1 - ρ * l) * (1 + ρ * (l / (1 - ρ * l)))) := by ring
    _ = l := by rw [h2, mul_one]

/-- Cochrane (2023), pp. 121–122 (selection by the transversality condition), **in a probability
model**: for `0 < ρ ≤ 1`, two equilibria with the same bounded adapted `i`, the same `e` and
`b₀`, whose values of debt satisfy the transversality condition, agree a.e. at every date. -/
theorem meqm_unique_tvc {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v x' p' v' : ℕ → Ω → ℝ}
    (h : MEqm S σ β κ ρ i e b0 x p v) (h' : MEqm S σ β κ ρ i e b0 x' p' v')
    (htvc : MTVC S ρ v) (htvc' : MTVC S ρ v') :
    ∀ t, x t =ᵐ[S.μ] x' t ∧ p t =ᵐ[S.μ] p' t ∧ v t =ᵐ[S.μ] v' t := by
  obtain ⟨hnk, hfl, h0, hxa, hpa, hva, hxb, hpb⟩ := h
  obtain ⟨hnk', hfl', h0', hxa', hpa', hva', hxb', hpb'⟩ := h'
  obtain ⟨-, -, hU, hS0, hS1⟩ := roots_nk hσ hκ hβ
  set lam := lS σ β κ
  set G := gainOf (nkP σ β κ) lam
  obtain ⟨hf, hEp⟩ := mnk_props S hσ hκ hβ hnk hxa hpa hxb hpb
  obtain ⟨hf', hEp'⟩ := mnk_props S hσ hκ hβ hnk' hxa' hpa' hxb' hpb'
  have hinv : |(lU σ β κ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lU σ β κ)]
    exact inv_lt_one_of_one_lt₀ hU
  have hff := S.forward_unique hinv hf hf'
    (fun t => ((fwd_adapted S hxa hpa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => ((fwd_adapted S hxa' hpa' t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fwd_bdd S hxb hpb) (fwd_bdd S hxb' hpb')
  have hpi := int_of S hpa hpb
  have hpi' := int_of S hpa' hpb'
  have hvi := htvc.1
  have hvi' := htvc'.1
  set d : ℕ → Ω → ℝ := fun t => p t - p' t with hd_def
  set w : ℕ → Ω → ℝ := fun t => v t - v' t with hw_def
  have hda : StronglyAdapted S.𝓕 d := fun t => (hpa t).sub (hpa' t)
  have hwa : StronglyAdapted S.𝓕 w := fun t => (hva t).sub (hva' t)
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => (hpi t).sub (hpi' t)
  have hwi : ∀ t, Integrable (w t) S.μ := fun t => (hvi t).sub (hvi' t)
  -- `E_t d_{t+1} = λ_S d_t`
  have hEd : ∀ t, S.E t (d (t + 1)) =ᵐ[S.μ] lam • d t := by
    intro t
    filter_upwards [S.E_sub (hpi (t + 1)) (hpi' (t + 1)) t, hEp t, hEp' t, hff t] with ω e1 e2 e3 e4
    simp only [hd_def, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e1 e2 e3 e4 ⊢
    rw [e1, e2, e3]
    simp only [fwd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e4 ⊢
    rw [e4]
    ring
  -- the flow of the differences
  have hwf : ∀ t, ∀ᵐ ω ∂S.μ, ρ * w (t + 1) ω = w t ω - d (t + 1) ω := by
    intro t
    filter_upwards [hfl t, hfl' t] with ω e1 e2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e1 e2
    simp only [hw_def, hd_def, Pi.sub_apply]
    linear_combination e1 - e2
  have hw0 : ∀ᵐ ω ∂S.μ, ρ * w 0 ω = -d 0 ω := by
    filter_upwards [h0, h0'] with ω e1 e2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e1 e2
    simp only [hw_def, hd_def, Pi.sub_apply]
    linear_combination e1 - e2
  have hρl : 1 - ρ * lam ≠ 0 := by nlinarith
  set c := lam / (1 - ρ * lam)
  have hcl := cW_eq (ρ := ρ) hρl
  -- `y = w − c d` solves `y_t = ρ E_t y_{t+1}`
  set y : ℕ → Ω → ℝ := fun t => w t - c • d t with hy_def
  have hyy : ∀ t, y t =ᵐ[S.μ] ρ • S.E t (y (t + 1)) := by
    intro t
    have hEw : ∀ᵐ ω ∂S.μ, ρ * S.E t (w (t + 1)) ω = w t ω - S.E t (d (t + 1)) ω := by
      have hwf' : (fun ω => ρ * w (t + 1) ω) =ᵐ[S.μ] fun ω => w t ω - d (t + 1) ω := hwf t
      filter_upwards [S.E_congr hwf' t, S.E_smul ρ (w (t + 1)) t,
        S.E_sub (hwi t) (hdi (t + 1)) t] with ω e1 e2 e3
      have e2' : S.E t (fun ω => ρ * w (t + 1) ω) ω = ρ * S.E t (w (t + 1)) ω := e2
      have e3' : S.E t (fun ω => w t ω - d (t + 1) ω) ω =
          S.E t (w t) ω - S.E t (d (t + 1)) ω := e3
      rw [← e2', e1, e3', S.E_of_stronglyMeasurable (hwa t) (hwi t)]
    filter_upwards [hEw, E_sub_smul S (hwi (t + 1)) (hdi (t + 1)) c t, hEd t] with ω e1 e2 e3
    simp only [hy_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e3 ⊢
    rw [e3] at e1
    rw [e2, e3]
    linear_combination (-1 : ℝ) * e1 + d t ω * hcl
  -- the transversality conditions force `y = 0`
  have hy0 : ∀ t, y t =ᵐ[S.μ] 0 := by
    intro t
    have hEdk := E_iter S hda hdi hEd t
    have hk : ∀ k : ℕ, ∀ᵐ ω ∂S.μ, y t ω = ρ ^ (k + 1) * S.E t (v (t + (k + 1))) ω -
        ρ ^ (k + 1) * S.E t (v' (t + (k + 1))) ω - c * (ρ * lam) ^ (k + 1) * d t ω := by
      intro k
      filter_upwards [S.iterate_homog hyy t k, E_sub_smul S (hwi (t + (k + 1)))
        (hdi (t + (k + 1))) c t, S.E_sub (hvi (t + (k + 1))) (hvi' (t + (k + 1))) t,
        hEdk (k + 1)] with ω e1 e2 e3 e4
      rw [e1, Pi.smul_apply, smul_eq_mul]
      have e2' : S.E t (y (t + (k + 1))) ω = S.E t (w (t + (k + 1))) ω -
          c * S.E t (d (t + (k + 1))) ω := e2
      have e3' : S.E t (w (t + (k + 1))) ω = S.E t (v (t + (k + 1))) ω -
          S.E t (v' (t + (k + 1))) ω := e3
      rw [e2', e3', e4]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    filter_upwards [ae_all_iff.2 hk, htvc.2 t, htvc'.2 t] with ω hk1 hT hT'
    have hq0 : 0 ≤ ρ * lam := by positivity
    have hq1 : ρ * lam < 1 := by nlinarith
    have hg : Tendsto (fun k : ℕ => c * (ρ * lam) ^ (k + 1) * d t ω) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
        (tendsto_add_atTop_nat 1)).const_mul c
      rw [mul_zero] at this
      have h2 := this.mul_const (d t ω)
      rw [zero_mul] at h2
      exact h2
    have hT1 := hT.comp (tendsto_add_atTop_nat 1)
    have hT1' := hT'.comp (tendsto_add_atTop_nat 1)
    have hlim := (hT1.sub hT1').sub hg
    rw [sub_zero, sub_zero] at hlim
    have hconst : Tendsto (fun _ : ℕ => y t ω) atTop (𝓝 (y t ω)) := tendsto_const_nhds
    have := tendsto_nhds_unique (hconst.congr fun k => by
      simp only [Function.comp_apply]
      exact hk1 k) hlim
    simpa using this
  have hwd : ∀ t, ∀ᵐ ω ∂S.μ, w t ω = c * d t ω := by
    intro t
    filter_upwards [hy0 t] with ω e
    simp only [hy_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
    linarith
  have h1c : 1 + ρ * c ≠ 0 := by
    have : 1 + ρ * c = 1 / (1 - ρ * lam) := by
      simp only [c]
      field_simp
      ring
    rw [this]
    exact one_div_ne_zero hρl
  have hdz : ∀ t, d t =ᵐ[S.μ] 0 := by
    intro t
    induction t with
    | zero =>
      filter_upwards [hw0, hwd 0] with ω e1 e2
      rw [e2] at e1
      have : (1 + ρ * c) * d 0 ω = 0 := by linarith
      simpa [h1c] using this
    | succ t ih =>
      filter_upwards [hwf t, hwd t, hwd (t + 1), ih] with ω e1 e2 e3 e4
      rw [e2, e3, e4] at e1
      simp only [Pi.zero_apply, mul_zero, zero_sub] at e1 e4 ⊢
      have : (1 + ρ * c) * d (t + 1) ω = 0 := by linarith
      simpa [h1c] using this
  intro t
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hff t, hdz t] with ω e1 e2
    simp only [fwd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1
    simp only [hd_def, Pi.sub_apply, Pi.zero_apply] at e2
    have : p t ω = p' t ω := by linarith
    rw [this] at e1
    linarith
  · filter_upwards [hdz t] with ω e
    simp only [hd_def, Pi.sub_apply, Pi.zero_apply] at e
    linarith
  · filter_upwards [hwd t, hdz t] with ω e1 e2
    simp only [Pi.zero_apply] at e2
    rw [e2, mul_zero] at e1
    simp only [hw_def, Pi.sub_apply] at e1
    linarith

/-- Cochrane (2023), p. 121 (tool): a bounded process satisfies the transversality condition for
`0 ≤ ρ < 1`. -/
theorem mtvc_of_bdd {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v : ℕ → Ω → ℝ}
    (hva : StronglyAdapted S.𝓕 v) (hvb : S.BddProc v) : MTVC S ρ v := by
  refine ⟨int_of S hva hvb, fun t => ?_⟩
  obtain ⟨M, hM⟩ := hvb
  filter_upwards [ae_all_iff.2 fun k => S.abs_E_le (hM (t + k)) t] with ω hb
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const M
  rw [zero_mul] at hg
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) hg
  rw [Function.comp_apply, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
  exact mul_le_mul_of_nonneg_left (hb k) (pow_nonneg hρ0 k)

/-- Cochrane (2023), p. 121 ("ρ ≤ 1 provides the additional forward-looking root"), **in a
probability model**: for `0 < ρ < 1`, two equilibria with bounded values of debt and the same
data agree a.e. at every date. -/
theorem meqm_unique {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v x' p' v' : ℕ → Ω → ℝ}
    (h : MEqm S σ β κ ρ i e b0 x p v) (h' : MEqm S σ β κ ρ i e b0 x' p' v')
    (hvb : S.BddProc v) (hvb' : S.BddProc v') :
    ∀ t, x t =ᵐ[S.μ] x' t ∧ p t =ᵐ[S.μ] p' t ∧ v t =ᵐ[S.μ] v' t :=
  meqm_unique_tvc S hσ hκ hβ hρ0 hρ1.le h h' (mtvc_of_bdd S hρ0.le hρ1 h.2.2.2.2.2.1 hvb)
    (mtvc_of_bdd S hρ0.le hρ1 h'.2.2.2.2.2.1 hvb')

/-! ### Existence -/

/-- Cochrane (2023), p. 121 (construction of the solution): inflation from the flow,
`D π_0 = b_0 − e_0 − ρ y_0`, `D π_{t+1} = y_t + c π_t − e_{t+1} − ρ y_{t+1}`, where `y` is the
forward-solved part of debt and `v = y + cπ`. -/
noncomputable def pRec (D c ρ : ℝ) (y e : ℕ → Ω → ℝ) (b0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => D⁻¹ • (b0 - e 0 - ρ • y 0)
  | t + 1 => D⁻¹ • (y t + c • pRec D c ρ y e b0 t - e (t + 1) - ρ • y (t + 1))

/-- Cochrane (2023), p. 121 (tool): `pRec` is adapted. -/
theorem pRec_adapted {D c ρ : ℝ} {y e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hya : StronglyAdapted S.𝓕 y)
    (hea : StronglyAdapted S.𝓕 e) (hb0 : StronglyMeasurable[S.𝓕 0] b0) :
    StronglyAdapted S.𝓕 (pRec D c ρ y e b0) := by
  intro t
  induction t with
  | zero => exact (((hb0.sub (hea 0)).sub ((hya 0).const_smul ρ))).const_smul _
  | succ t ih =>
    have hm : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
    exact ((((hya t).mono hm).add ((ih.mono hm).const_smul c)).sub (hea (t + 1)) |>.sub
      ((hya (t + 1)).const_smul ρ)).const_smul _

/-- Cochrane (2023), p. 121 (tool): `pRec` is bounded when `y`, `e`, `b₀` are and
`c/D ∈ [0, 1)`. -/
theorem pRec_bdd {D c ρ : ℝ} (hD : 0 < D) (hcD0 : 0 ≤ c / D) (hcD1 : c / D < 1)
    {y e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hyb : S.BddProc y) (heb : S.BddProc e)
    {B : ℝ} (hb0 : ∀ᵐ ω ∂S.μ, |b0 ω| ≤ B) : S.BddProc (pRec D c ρ y e b0) := by
  obtain ⟨My, hMy⟩ := hyb
  obtain ⟨Me, hMe⟩ := heb
  set H := D⁻¹ * (My + Me + |ρ| * My)
  set B0 := D⁻¹ * (|B| + Me + |ρ| * My)
  have hDi : 0 < D⁻¹ := inv_pos.mpr hD
  have hstep : ∀ t, ∀ᵐ ω ∂S.μ, |pRec D c ρ y e b0 (t + 1) ω -
      c / D * pRec D c ρ y e b0 t ω| ≤ H := by
    intro t
    filter_upwards [hMy t, hMy (t + 1), hMe (t + 1)] with ω h1 h2 h3
    have hq : pRec D c ρ y e b0 (t + 1) ω - c / D * pRec D c ρ y e b0 t ω =
        D⁻¹ * (y t ω - e (t + 1) ω - ρ * y (t + 1) ω) := by
      simp only [pRec, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
      field_simp
      ring
    rw [hq, abs_mul, abs_of_pos hDi]
    refine mul_le_mul_of_nonneg_left ?_ hDi.le
    calc |y t ω - e (t + 1) ω - ρ * y (t + 1) ω| ≤
          |y t ω| + |e (t + 1) ω| + |ρ| * |y (t + 1) ω| := by
          rw [← abs_mul]
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ My + Me + |ρ| * My := by gcongr
  have h0 : ∀ᵐ ω ∂S.μ, |pRec D c ρ y e b0 0 ω| ≤ B0 := by
    filter_upwards [hb0, hMy 0, hMe 0] with ω h1 h2 h3
    simp only [pRec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos hDi]
    refine mul_le_mul_of_nonneg_left ?_ hDi.le
    calc |b0 ω - e 0 ω - ρ * y 0 ω| ≤ |b0 ω| + |e 0 ω| + |ρ| * |y 0 ω| := by
          rw [← abs_mul]
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ |B| + Me + |ρ| * My := add_le_add (add_le_add (h1.trans (le_abs_self B)) h3)
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg ρ))
  have hH : 0 ≤ H := by
    obtain ⟨ω, hω⟩ := (hstep 0).exists
    exact (abs_nonneg _).trans hω
  have hB0 : 0 ≤ B0 := by
    obtain ⟨ω, hω⟩ := h0.exists
    exact (abs_nonneg _).trans hω
  refine ⟨B0 + H / (1 - c / D), fun t => ?_⟩
  induction t with
  | zero =>
    filter_upwards [h0] with ω h
    have : 0 ≤ H / (1 - c / D) := div_nonneg hH (by linarith)
    linarith
  | succ t ih =>
    filter_upwards [ih, hstep t] with ω h1 h2
    have hq : pRec D c ρ y e b0 (t + 1) ω = (pRec D c ρ y e b0 (t + 1) ω -
        c / D * pRec D c ρ y e b0 t ω) + c / D * pRec D c ρ y e b0 t ω := by ring
    rw [hq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hcD0]
    have hk : H / (1 - c / D) * (1 - c / D) = H := div_mul_cancel₀ _ (by linarith)
    nlinarith

/-- Cochrane (2023), p. 121 (tool, the algebra of the construction): if
`y = ρ E y' + (E e' − k f)` with `λ D = c` and `k = D κ/β`, then
`D⁻¹((y + cπ) − (E e' + ρ E y')) = λπ − (κ/β) f`. -/
theorem alg_exist {D c k lam kb Y P Ee Ey F ρ : ℝ} (hD : D ≠ 0) (hcl : lam * D = c)
    (hk : k = D * kb) (hy : Y = ρ * Ey + (Ee - k * F)) :
    D⁻¹ * ((Y + c * P) - (Ee + ρ * Ey)) = lam * P - kb * F := by
  subst hcl hk
  rw [hy]
  field_simp
  ring

/-- Cochrane (2023), p. 121 ("ρ ≤ 1 provides the additional forward-looking root"), **existence
in a probability model**: for `0 < ρ < 1`, bounded adapted `i`, `e` and a bounded
`𝓕₀`-measurable `b₀`, the model (5.15)–(5.16) has an equilibrium with bounded debt. -/
theorem meqm_exists {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hia : StronglyAdapted S.𝓕 i)
    (hib : S.BddProc i) (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e)
    (hb0 : StronglyMeasurable[S.𝓕 0] b0) {B : ℝ} (hb0b : ∀ᵐ ω ∂S.μ, |b0 ω| ≤ B) :
    ∃ x p v, MEqm S σ β κ ρ i e b0 x p v ∧ S.BddProc v := by
  obtain ⟨hsum, hprod, hU, hS0, hS1⟩ := roots_nk hσ hκ hβ
  set lam := lS σ β κ
  set G := gainOf (nkP σ β κ) lam
  have hβ' : (nkP σ β κ).beta ≠ 0 := by simpa [nkP] using hβ.ne'
  have hκ' : (nkP σ β κ).kappa ≠ 0 := by simpa [nkP] using hκ.ne'
  have hU0 : lU σ β κ ≠ 0 := by linarith
  have hinv : |(lU σ β κ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lU σ β κ)]
    exact inv_lt_one_of_one_lt₀ hU
  have hρabs : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hρl : 0 < 1 - ρ * lam := by nlinarith
  set c := lam / (1 - ρ * lam)
  set D := 1 + ρ * c
  have hD : D = 1 / (1 - ρ * lam) := by
    simp only [D, c]
    field_simp
    ring
  have hDpos : 0 < D := by rw [hD]; positivity
  have hcl : lam * D = c := cW_eq hρl.ne'
  have hcD : c / D = lam := by rw [← hcl]; field_simp
  set k := D * (κ / β)
  -- the forward part `f`
  obtain ⟨Mi, hMi⟩ := hib
  have hib' : ∀ t, ∀ᵐ ω ∂S.μ, |((fun t => (-(σ / lU σ β κ)) • i t) t) ω| ≤ |σ / lU σ β κ| * Mi :=
    fun t => by
      filter_upwards [hMi t] with ω h
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hia' : StronglyAdapted S.𝓕 (fun t => (-(σ / lU σ β κ)) • i t) :=
    fun t => (hia t).const_smul _
  set F := S.forwardSol (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t)
  have hFs := S.forwardSol_solves hinv hia' hib'
  have hFa : StronglyAdapted S.𝓕 F := S.forwardSol_adapted _ _
  have hFb : S.BddProc F := S.forwardSol_bdd hinv hib'
  -- the forward-solved part of debt `y`
  obtain ⟨Me, hMe⟩ := heb
  obtain ⟨MF, hMF⟩ := hFb
  set u : ℕ → Ω → ℝ := fun t => S.E t (e (t + 1)) - k • F t
  have hua : StronglyAdapted S.𝓕 u := fun t =>
    (S.stronglyMeasurable_E t _).sub ((hFa t).const_smul k)
  have hub : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ Me + |k| * MF := fun t => by
    filter_upwards [S.abs_E_le (hMe (t + 1)) t, hMF t] with ω h1 h2
    simp only [u, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add h1 ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  set y := S.forwardSol ρ u
  have hys := S.forwardSol_solves hρabs hua hub
  have hya : StronglyAdapted S.𝓕 y := S.forwardSol_adapted _ _
  have hyb : S.BddProc y := S.forwardSol_bdd hρabs hub
  -- inflation and debt
  set p := pRec D c ρ y e b0
  have hpa : StronglyAdapted S.𝓕 p := pRec_adapted S hya hea hb0
  have hpb : S.BddProc p := pRec_bdd S hDpos (by rw [hcD]; exact hS0.le) (by rw [hcD]; exact hS1)
    hyb ⟨Me, hMe⟩ hb0b
  have hyi := int_of S hya hyb
  have hpi := int_of S hpa hpb
  have hei := int_of S hea ⟨Me, hMe⟩
  have hFi := int_of S hFa ⟨MF, hMF⟩
  -- `E_t π_{t+1} = λ_S π_t − (κ/β) f_t`
  have hEp : ∀ t, ∀ᵐ ω ∂S.μ, S.E t (p (t + 1)) ω = lam * p t ω - κ / β * F t ω := by
    intro t
    have hpt : p (t + 1) = D⁻¹ • ((y t + c • p t) - (e (t + 1) + ρ • y (t + 1))) := by
      simp only [p, pRec]
      congr 1
      abel
    have hm1 : StronglyMeasurable[S.𝓕 t] (y t + c • p t) := (hya t).add ((hpa t).const_smul c)
    have hi1 : Integrable (y t + c • p t) S.μ := (hyi t).add ((hpi t).smul c)
    filter_upwards [S.E_smul D⁻¹ ((y t + c • p t) - (e (t + 1) + ρ • y (t + 1))) t,
      S.E_sub hi1 ((hei (t + 1)).add ((hyi (t + 1)).smul ρ)) t,
      E_add_smul S (hei (t + 1)) (hyi (t + 1)) ρ t, hys t] with ω e1 e2 e3 e4
    rw [hpt, e1, Pi.smul_apply, e2, Pi.sub_apply, S.E_of_stronglyMeasurable hm1 hi1, e3]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e4 ⊢
    exact alg_exist hDpos.ne' hcl rfl e4
  -- `E_t f_{t+1} = λ_U f_t + σ i_t`
  have hEF : ∀ t, ∀ᵐ ω ∂S.μ, S.E t (F (t + 1)) ω = lU σ β κ * F t ω + σ * i t ω := by
    intro t
    filter_upwards [hFs t] with ω hq
    have h2 : F t ω = (lU σ β κ)⁻¹ * S.E t (F (t + 1)) ω + -(σ / lU σ β κ) * i t ω := hq
    rw [h2]
    field_simp
    ring
  refine ⟨fun t => F t + G • p t, p, fun t => y t + c • p t, ⟨⟨fun t => ?_, fun t => ?_⟩,
    fun t => ?_, ?_, fun t => (hFa t).add ((hpa t).const_smul G), hpa,
    fun t => (hya t).add ((hpa t).const_smul c), mbdd_add S ⟨MF, hMF⟩ (mbdd_smul S G hpb),
    hpb⟩, mbdd_add S hyb (mbdd_smul S c hpb)⟩
  · filter_upwards [hEp t, hEF t, E_add_smul S (hFi (t + 1)) (hpi (t + 1)) G t] with ω e1 e2 e3
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e3, e2, e1]
    have := (blk_exist_pt (P := nkP σ β κ) hβ' hκ' hsum hprod (F := F t ω) (Pp := p t ω)
      (U := i t ω) rfl rfl).1
    have q1 : (nkP σ β κ).thIpi = 0 := rfl
    have q2 : (nkP σ β κ).thIx = 0 := rfl
    have q3 : (nkP σ β κ).sigma = σ := rfl
    have q4 : (nkP σ β κ).kappa = κ := rfl
    have q5 : (nkP σ β κ).beta = β := rfl
    rw [q1, q2, q3, q4, q5] at this
    simp only [zero_mul, zero_add] at this
    linarith
  · filter_upwards [hEp t] with ω e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1]
    have := (blk_exist_pt (P := nkP σ β κ) hβ' hκ' hsum hprod (F := F t ω) (Pp := p t ω)
      (U := i t ω) rfl rfl).2
    exact this
  · refine Eventually.of_forall fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, p, pRec]
    field_simp
    simp only [D]
    ring
  · refine Eventually.of_forall fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, p, pRec]
    field_simp
    simp only [D]
    ring

/-- Cochrane (2023), pp. 121–122, **determinacy in a probability model**: for `0 < ρ < 1`, bounded
adapted `i`, `e` and a bounded `𝓕₀`-measurable `b₀`, the model (5.15)–(5.16) has an
equilibrium with bounded debt, and any two such equilibria agree a.e. at every date. -/
theorem meqm_determinate {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hia : StronglyAdapted S.𝓕 i)
    (hib : S.BddProc i) (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e)
    (hb0 : StronglyMeasurable[S.𝓕 0] b0) {B : ℝ} (hb0b : ∀ᵐ ω ∂S.μ, |b0 ω| ≤ B) :
    (∃ x p v, MEqm S σ β κ ρ i e b0 x p v ∧ S.BddProc v) ∧
      ∀ x p v x' p' v', MEqm S σ β κ ρ i e b0 x p v → S.BddProc v →
        MEqm S σ β κ ρ i e b0 x' p' v' → S.BddProc v' →
          ∀ t, x t =ᵐ[S.μ] x' t ∧ p t =ᵐ[S.μ] p' t ∧ v t =ᵐ[S.μ] v' t :=
  ⟨meqm_exists S hσ hκ hβ hρ0 hρ1 hia hib hea heb hb0 hb0b,
    fun _ _ _ _ _ _ h hv h' hv' => meqm_unique S hσ hκ hβ hρ0 hρ1 h h' hv hv'⟩

/-! ### (5.3) and (5.4) -/

/-- Cochrane (2023), eq. (5.4), p. 119, **in a probability model**: for `0 < β < 1` and bounded
adapted `x, π` satisfying the Phillips curve a.e., `π_t = ∑_k βᵏ κ E_t x_{t+k}` a.e. (a genuine
convergent series). -/
theorem mpc_forward {β κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {x p : ℕ → Ω → ℝ}
    (hpc : ∀ t, p t =ᵐ[S.μ] β • S.E t (p (t + 1)) + κ • x t) (hxa : StronglyAdapted S.𝓕 x)
    (hpa : StronglyAdapted S.𝓕 p) (hxb : S.BddProc x) (hpb : S.BddProc p) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => β ^ k * (κ * S.E t (x (t + k)) ω)) (p t ω) := by
  have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  obtain ⟨Mx, hMx⟩ := hxb
  have hub : ∀ t, ∀ᵐ ω ∂S.μ, |(κ • x) t ω| ≤ |κ| * Mx := fun t => by
    filter_upwards [hMx t] with ω h
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg κ)
  have hua : StronglyAdapted S.𝓕 (κ • x) := fun t => (hxa t).const_smul κ
  have hsol : S.Solves β (κ • x) p := fun t => by simpa using hpc t
  have heq := S.forward_unique hβ hsol (S.forwardSol_solves hβ hua hub)
    (fun t => ((hpa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => ((S.forwardSol_adapted β _ t).mono (S.𝓕.le t)).aestronglyMeasurable) hpb
    (S.forwardSol_bdd hβ hub) t
  filter_upwards [heq, S.forwardSol_hasSum hβ
    (fun t => ((hua t).mono (S.𝓕.le t)).aestronglyMeasurable) hub t,
    ae_all_iff.2 fun k => S.E_smul κ (x (t + k)) t] with ω e1 e2 e3
  rw [e1]
  convert e2 using 2 with k
  rw [show (κ • x) (t + k) = κ • x (t + k) from rfl, e3 k]
  rfl

/-- Cochrane (2023), eq. (5.3), p. 118, **in a probability model**: iterating the IS curve,
`x_t = E_t x_{t+k} − σ ∑_{j<k} (E_t i_{t+j} − E_t π_{t+j+1})` a.e., for bounded adapted
`x, π, i`. -/
theorem mis_iterate {σ : ℝ} {i x p : ℕ → Ω → ℝ}
    (his : ∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • (i t - S.E t (p (t + 1))))
    (hxa : StronglyAdapted S.𝓕 x) (hia : StronglyAdapted S.𝓕 i) (hpa : StronglyAdapted S.𝓕 p)
    (hxb : S.BddProc x) (hib : S.BddProc i) (hpb : S.BddProc p) (t : ℕ) :
    ∀ k, ∀ᵐ ω ∂S.μ, x t ω = S.E t (x (t + k)) ω -
      σ * ∑ j ∈ Finset.range k, (S.E t (i (t + j)) ω - S.E t (p (t + j + 1)) ω) := by
  have hxi := int_of S hxa hxb
  have hii := int_of S hia hib
  have hpi := int_of S hpa hpb
  intro k
  induction k with
  | zero =>
    refine Eventually.of_forall fun ω => ?_
    simp [E_self S hxa hxb t]
  | succ k ih =>
    have hA := S.integrable_E (t + k) (x (t + k + 1))
    have hC := S.integrable_E (t + k) (p (t + k + 1))
    filter_upwards [ih, S.E_congr (his (t + k)) t,
      E_sub_smul S hA ((hii (t + k)).sub hC) σ t, S.E_sub (hii (t + k)) hC t,
      S.E_tower (Nat.le_add_right t k) (x (t + k + 1)),
      S.E_tower (Nat.le_add_right t k) (p (t + k + 1))] with ω e1 e2 e3 e4 e5 e6
    rw [e1, e2, e3, e4, Pi.sub_apply, e5, e6, Finset.sum_range_succ]
    ring_nf

/-- Cochrane (2023), eq. (5.3), p. 118, **the limit form in a probability model**: a.e., the
partial sums `∑_{j<k} (E_t i_{t+j} − E_t π_{t+j+1})` converge to `−x_t/σ` iff
`E_t x_{t+k} → 0` (`σ ≠ 0`). -/
theorem mis_iterate_limit {σ : ℝ} (hσ : σ ≠ 0) {i x p : ℕ → Ω → ℝ}
    (his : ∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • (i t - S.E t (p (t + 1))))
    (hxa : StronglyAdapted S.𝓕 x) (hia : StronglyAdapted S.𝓕 i) (hpa : StronglyAdapted S.𝓕 p)
    (hxb : S.BddProc x) (hib : S.BddProc i) (hpb : S.BddProc p) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (Tendsto (fun k => S.E t (x (t + k)) ω) atTop (𝓝 0) ↔
      Tendsto (fun k => ∑ j ∈ Finset.range k, (S.E t (i (t + j)) ω - S.E t (p (t + j + 1)) ω))
        atTop (𝓝 (-(x t ω / σ)))) := by
  filter_upwards [ae_all_iff.2 (mis_iterate S his hxa hia hpa hxb hib hpb t)] with ω h
  have e : ∀ k, ∑ j ∈ Finset.range k, (S.E t (i (t + j)) ω - S.E t (p (t + j + 1)) ω) =
      (S.E t (x (t + k)) ω - x t ω) / σ := fun k => by
    rw [eq_div_iff hσ]
    linarith [h k]
  simp_rw [e]
  constructor
  · intro h0
    have := (h0.sub_const (x t ω)).div_const σ
    rwa [zero_sub, neg_div] at this
  · intro h1
    have := (h1.const_mul σ).add_const (x t ω)
    have e2 : σ * -(x t ω / σ) + x t ω = 0 := by field_simp; ring
    rw [e2] at this
    refine this.congr fun k => ?_
    field_simp
    ring

/-! ### `ρ = 1`: boundedness does not select (E20/E32) -/

/-- Cochrane (2023), p. 121 and survey E20/E32 (the perturbation at `ρ = 1`): inflation
`dπ_t = −(1 − λ_S)λ_Sᵗ`. -/
noncomputable def dPi (l : ℝ) (t : ℕ) : ℝ := -(1 - l) * l ^ t

/-- Cochrane (2023), p. 121 and E20/E32 (the perturbation at `ρ = 1`): debt
`dv_t = 1 − λ_S^{t+1}`. -/
noncomputable def dV (l : ℝ) (t : ℕ) : ℝ := 1 - l ^ (t + 1)

/-- Cochrane (2023), p. 121 ("ρ ≤ 1 provides the additional forward-looking root") and survey
E20/E32, **in a probability model**: at `ρ = 1` every equilibrium `(x, π, v)` has a companion
equilibrium with the same data, `(x + g dπ, π + dπ, v + dv)` with deterministic bounded `dπ_t = −(1
− λ_S)λ_Sᵗ`, `dv_t = 1 − λ_S^{t+1}`; it is bounded when `v` is, and its date-0 inflation differs
from `π_0` everywhere by `−(1 − λ_S) ≠ 0`. -/
theorem rho_one_not_unique {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ} (h : MEqm S σ β κ 1 i e b0 x p v) :
    MEqm S σ β κ 1 i e b0
        (fun t ω => x t ω + gainOf (nkP σ β κ) (lS σ β κ) * dPi (lS σ β κ) t)
        (fun t ω => p t ω + dPi (lS σ β κ) t) (fun t ω => v t ω + dV (lS σ β κ) t) ∧
      (S.BddProc v → S.BddProc (fun t ω => v t ω + dV (lS σ β κ) t)) ∧
      ∀ ω, p 0 ω + dPi (lS σ β κ) 0 ≠ p 0 ω := by
  obtain ⟨hsum, hprod, -, hS0, hS1⟩ := roots_nk hσ hκ hβ
  have hβ' : (nkP σ β κ).beta ≠ 0 := by simpa [nkP] using hβ.ne'
  have hκ' : (nkP σ β κ).kappa ≠ 0 := by simpa [nkP] using hκ.ne'
  set l := lS σ β κ
  set G := gainOf (nkP σ β κ) l
  obtain ⟨⟨his, hpc⟩, hfl, h0, hxa, hpa, hva, hxb, hpb⟩ := h
  have hxi := int_of S hxa hxb
  have hpi := int_of S hpa hpb
  -- the deterministic perturbation solves the homogeneous block
  have hblk : ∀ t, 0 + G * dPi l t = (0 + G * dPi l (t + 1)) - σ * (0 * dPi l t +
      0 * (0 + G * dPi l t) + 0 - dPi l (t + 1)) ∧
      dPi l t = β * dPi l (t + 1) + κ * (0 + G * dPi l t) := by
    intro t
    have hd : dPi l (t + 1) = l * dPi l t := by simp only [dPi, pow_succ]; ring
    have := blk_exist_pt (P := nkP σ β κ) hβ' hκ' hsum hprod (F := 0) (Pp := dPi l t) (U := 0)
      (EF := 0) (EP := dPi l (t + 1)) (by ring) (by rw [hd]; ring)
    exact this
  have hEc : ∀ t (y : Ω → ℝ) (c : ℝ), Integrable y S.μ →
      ∀ᵐ ω ∂S.μ, S.E t (fun ω => y ω + c) ω = S.E t y ω + c := by
    intro t y c hy
    filter_upwards [S.E_add hy (integrable_const c) t] with ω h1
    have h2 : (fun ω => y ω + c) = y + fun _ => c := rfl
    rw [h2, h1, Pi.add_apply, S.E_const]
  refine ⟨⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    ?_, ?_⟩, ?_, fun ω => ?_⟩
  · filter_upwards [his t, hEc t (x (t + 1)) (G * dPi l (t + 1)) (hxi (t + 1)),
      hEc t (p (t + 1)) (dPi l (t + 1)) (hpi (t + 1))] with ω e1 e2 e3
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [e2, e3, e1]
    have := (hblk t).1
    simp only [zero_mul, zero_add, add_zero] at this
    linarith
  · filter_upwards [hpc t, hEc t (p (t + 1)) (dPi l (t + 1)) (hpi (t + 1))] with ω e1 e3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [e3, e1]
    have := (hblk t).2
    simp only [zero_add] at this
    linarith
  · filter_upwards [hfl t] with ω e1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul] at e1 ⊢
    rw [e1]
    simp only [dV, dPi, pow_succ]
    ring
  · filter_upwards [h0] with ω e1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul] at e1 ⊢
    rw [e1]
    simp only [dV, dPi]
    ring
  · exact (hxa t).add stronglyMeasurable_const
  · exact (hpa t).add stronglyMeasurable_const
  · exact (hva t).add stronglyMeasurable_const
  · obtain ⟨M, hM⟩ := hxb
    refine ⟨M + |G| * (1 - l), fun t => ?_⟩
    filter_upwards [hM t] with ω h1
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simp only [dPi, abs_mul, abs_neg, abs_pow, abs_of_pos hS0, abs_of_pos (by linarith : 0 < 1 - l)]
    exact mul_le_of_le_one_right (by linarith) (pow_le_one₀ hS0.le hS1.le)
  · obtain ⟨M, hM⟩ := hpb
    refine ⟨M + (1 - l), fun t => ?_⟩
    filter_upwards [hM t] with ω h1
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    simp only [dPi, abs_mul, abs_neg, abs_pow, abs_of_pos hS0, abs_of_pos (by linarith : 0 < 1 - l)]
    exact mul_le_of_le_one_right (by linarith) (pow_le_one₀ hS0.le hS1.le)
  · rintro ⟨M, hM⟩
    refine ⟨M + 1, fun t => ?_⟩
    filter_upwards [hM t] with ω h1
    refine (abs_add_le _ _).trans (add_le_add h1 ?_)
    have h2 : 0 ≤ l ^ (t + 1) := pow_nonneg hS0.le _
    have h3 : l ^ (t + 1) ≤ 1 := pow_le_one₀ hS0.le hS1.le
    simp only [dV]
    rw [abs_le]
    constructor <;> linarith
  · simp only [dPi, pow_zero, mul_one]
    intro h
    linarith

/-! ### (5.11)–(5.13): valuation and unexpected inflation -/

/-- Cochrane (2023), eqs. (5.11)–(5.12), p. 120, **in a probability model**: in a bounded
equilibrium with `0 < ρ < 1` and bounded adapted `e`, the value of debt is the present value
`v_t = ∑_k ρᵏ E_t(π_{t+1+k} + e_{t+1+k})` a.e. (genuine series). -/
theorem mvaluation {σ β κ ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {i e : ℕ → Ω → ℝ}
    {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ} (h : MEqm S σ β κ ρ i e b0 x p v)
    (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e) (hvb : S.BddProc v) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => ρ ^ k * S.E t (fun ω' => p (t + k + 1) ω' + e (t + k + 1) ω') ω)
      (v t ω) := by
  obtain ⟨-, hfl, -, -, hpa, hva, -, hpb⟩ := h
  have hρ : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hpi := int_of S hpa hpb
  have hei := int_of S hea heb
  have hvi := int_of S hva hvb
  set u : ℕ → Ω → ℝ := fun t => S.E t (fun ω' => p (t + 1) ω' + e (t + 1) ω')
  obtain ⟨Mp, hMp⟩ := hpb
  obtain ⟨Me, hMe⟩ := heb
  have hub : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ Mp + Me := fun t => S.abs_E_le (by
    filter_upwards [hMp (t + 1), hMe (t + 1)] with ω h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)) t
  have hua : StronglyAdapted S.𝓕 u := fun t => S.stronglyMeasurable_E t _
  have hsol : S.Solves ρ u v := by
    intro t
    have hv' : (fun ω => v t ω) =ᵐ[S.μ] fun ω => ρ * v (t + 1) ω + (p (t + 1) ω + e (t + 1) ω) := by
      filter_upwards [hfl t] with ω e1
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e1
      linarith
    filter_upwards [S.E_congr hv' t, E_add_smul S ((hpi (t + 1)).add (hei (t + 1)))
      (hvi (t + 1)) ρ t] with ω e1 e2
    have e3 : S.E t (fun ω => v t ω) ω = v t ω := by
      rw [show (fun ω => v t ω) = v t from rfl, S.E_of_stronglyMeasurable (hva t) (hvi t)]
    have e2' : S.E t (fun ω => ρ * v (t + 1) ω + (p (t + 1) ω + e (t + 1) ω)) ω =
        S.E t (fun ω' => p (t + 1) ω' + e (t + 1) ω') ω + ρ * S.E t (v (t + 1)) ω := by
      rw [show (fun ω => ρ * v (t + 1) ω + (p (t + 1) ω + e (t + 1) ω)) =
          (p (t + 1) + e (t + 1)) + ρ • v (t + 1) from by
        funext ω'
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring]
      exact e2
    rw [← e3, e1, e2']
    simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq := S.forward_unique hρ hsol (S.forwardSol_solves hρ hua hub)
    (fun t => ((hva t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => ((S.forwardSol_adapted ρ _ t).mono (S.𝓕.le t)).aestronglyMeasurable)
    hvb (S.forwardSol_bdd hρ hub) t
  filter_upwards [heq, S.forwardSol_hasSum hρ
    (fun t => ((hua t).mono (S.𝓕.le t)).aestronglyMeasurable) hub t,
    ae_all_iff.2 fun k => S.E_tower (Nat.le_add_right t k)
      (fun ω' => p (t + k + 1) ω' + e (t + k + 1) ω')] with ω e1 e2 e3
  rw [e1]
  convert e2 using 2 with k
  rw [← e3 k]

/-- Cochrane (2023), eq. (5.13), p. 120, **in a probability model**: the flow in innovations,
`ρ ΔE_{t+1} v_{t+1} = −ΔE_{t+1} π_{t+1} − ΔE_{t+1} e_{t+1}` a.e. (unexpected inflation is
pinned by news about debt and its forcing). -/
theorem mflow_innov {σ β κ ρ : ℝ} {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ}
    (h : MEqm S σ β κ ρ i e b0 x p v) (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e)
    (hvb : S.BddProc v) (t : ℕ) :
    ρ • S.innov t (v (t + 1)) =ᵐ[S.μ] -S.innov t (p (t + 1)) - S.innov t (e (t + 1)) := by
  obtain ⟨-, hfl, -, -, hpa, hva, -, hpb⟩ := h
  have hpi := int_of S hpa hpb
  have hei := int_of S hea heb
  have hvi := int_of S hva hvb
  have hfl' : (fun ω => ρ * v (t + 1) ω) =ᵐ[S.μ] fun ω => v t ω - (p (t + 1) ω + e (t + 1) ω) := by
    filter_upwards [hfl t] with ω e1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e1
    linarith
  filter_upwards [S.E_congr hfl' t, S.E_smul ρ (v (t + 1)) t, S.E_sub (hvi t)
    ((hpi (t + 1)).add (hei (t + 1))) t, S.E_add (hpi (t + 1)) (hei (t + 1)) t, hfl t]
    with ω e1 e2 e3 e4 e5
  simp only [MeasExpectationSystem.innov, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    smul_eq_mul, E_self S hva hvb (t + 1), E_self S hpa hpb (t + 1),
    S.E_of_stronglyMeasurable (hea (t + 1)) (hei (t + 1))]
  have e2' : S.E t (fun ω => ρ * v (t + 1) ω) ω = ρ * S.E t (v (t + 1)) ω := e2
  have e3' : S.E t (fun ω => v t ω - (p (t + 1) ω + e (t + 1) ω)) ω =
      S.E t (v t) ω - S.E t (p (t + 1) + e (t + 1)) ω := e3
  rw [e2', e3', e4, S.E_of_stronglyMeasurable (hva t) (hvi t)] at e1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e1 e5
  linarith

/-! ### One-period debt and long-term debt -/

/-- Cochrane (2023) (tool): an equilibrium stays one when the flow forcing is changed on a null
set at every date. -/
theorem meqm_congr {σ β κ ρ : ℝ} {i e e' : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ}
    (h : MEqm S σ β κ ρ i e b0 x p v) (he : ∀ t, e t =ᵐ[S.μ] e' t) :
    MEqm S σ β κ ρ i e' b0 x p v := by
  obtain ⟨h1, hfl, h0, rest⟩ := h
  refine ⟨h1, fun t => ?_, ?_, rest⟩
  · filter_upwards [hfl t, he (t + 1)] with ω e1 e2
    simp only [Pi.sub_apply] at e1 ⊢
    rw [e1, e2]
  · filter_upwards [h0, he 0] with ω e1 e2
    simp only [Pi.sub_apply] at e1 ⊢
    rw [e1, e2]

/-- Cochrane (2023), eqs. (5.15)–(5.16), p. 121, in a probability model: the sticky-price
fiscal-theory model with one-period debt, `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`, started
from the predetermined `b₀`, with adapted `x, π, v` and bounded `x, π`. -/
def MFTPLNK (σ β κ ρ : ℝ) (i s : ℕ → Ω → ℝ) (b0 : Ω → ℝ) (x p v : ℕ → Ω → ℝ) : Prop :=
  MNK S σ β κ i x p ∧ (∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + i t - p (t + 1) - s (t + 1)) ∧
  ρ • v 0 =ᵐ[S.μ] b0 - p 0 - s 0 ∧ StronglyAdapted S.𝓕 x ∧ StronglyAdapted S.𝓕 p ∧
  StronglyAdapted S.𝓕 v ∧ S.BddProc x ∧ S.BddProc p

/-- Cochrane (2023), eq. (5.16), p. 121, in a probability model: the one-period-debt model is the
general model with forcing `e = eShort i s` (`e_0 = s̃_0`, `e_{t+1} = s̃_{t+1} − i_t`). -/
theorem mftplnk_iff {σ β κ ρ : ℝ} {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ} :
    MFTPLNK S σ β κ ρ i s b0 x p v ↔ MEqm S σ β κ ρ i (FiscalNK.eShort i s) b0 x p v := by
  have hf : ∀ t, (v t + i t - p (t + 1) - s (t + 1)) =
      v t - p (t + 1) - FiscalNK.eShort i s (t + 1) := fun t => by
    rw [show FiscalNK.eShort i s (t + 1) = s (t + 1) - i t from rfl]
    abel
  have h0 : b0 - p 0 - s 0 = b0 - p 0 - FiscalNK.eShort i s 0 := rfl
  unfold MFTPLNK MEqm
  simp only [hf, h0]

/-- Cochrane (2023), eq. (5.16) (tool): `eShort i s` is adapted when `i` and `s` are. -/
theorem eShort_adaptedM {i s : ℕ → Ω → ℝ} (hia : StronglyAdapted S.𝓕 i)
    (hsa : StronglyAdapted S.𝓕 s) : StronglyAdapted S.𝓕 (FiscalNK.eShort i s) := by
  intro t
  cases t with
  | zero => exact hsa 0
  | succ t => exact (hsa (t + 1)).sub ((hia t).mono (S.𝓕.mono (Nat.le_succ t)))

/-- Cochrane (2023), eq. (5.16) (tool): `eShort i s` is bounded when `i` and `s` are. -/
theorem eShort_bddM {i s : ℕ → Ω → ℝ} (hib : S.BddProc i) (hsb : S.BddProc s) :
    S.BddProc (FiscalNK.eShort i s) := by
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Ms, hMs⟩ := hsb
  refine ⟨Ms + |Mi|, fun t => ?_⟩
  cases t with
  | zero =>
    filter_upwards [hMs 0] with ω h
    exact h.trans (le_add_of_nonneg_right (abs_nonneg _))
  | succ t =>
    filter_upwards [hMs (t + 1), hMi t] with ω h1 h2
    exact (abs_sub _ _).trans (add_le_add h1 (h2.trans (le_abs_self _)))

/-- Cochrane (2023), §5.1.2, p. 121, **determinacy with one-period debt in a probability model**:
for `0 < ρ < 1`, bounded adapted `i`, `s̃` and bounded `𝓕₀`-measurable `b₀`, the model
(5.15)–(5.16) has an equilibrium with bounded debt, unique a.e. at every date. -/
theorem mftplnk_determinate {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hia : StronglyAdapted S.𝓕 i)
    (hib : S.BddProc i) (hsa : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hb0 : StronglyMeasurable[S.𝓕 0] b0) {B : ℝ} (hb0b : ∀ᵐ ω ∂S.μ, |b0 ω| ≤ B) :
    (∃ x p v, MFTPLNK S σ β κ ρ i s b0 x p v ∧ S.BddProc v) ∧
      ∀ x p v x' p' v', MFTPLNK S σ β κ ρ i s b0 x p v → S.BddProc v →
        MFTPLNK S σ β κ ρ i s b0 x' p' v' → S.BddProc v' →
          ∀ t, x t =ᵐ[S.μ] x' t ∧ p t =ᵐ[S.μ] p' t ∧ v t =ᵐ[S.μ] v' t := by
  obtain ⟨⟨x, p, v, h, hv⟩, hu⟩ := meqm_determinate S hσ hκ hβ hρ0 hρ1 hia hib
    (eShort_adaptedM S hia hsa) (eShort_bddM S hib hsb) hb0 hb0b
  refine ⟨⟨x, p, v, (mftplnk_iff S).2 h, hv⟩, fun x p v x' p' v' h hv h' hv' => ?_⟩
  exact hu x p v x' p' v' ((mftplnk_iff S).1 h) hv ((mftplnk_iff S).1 h') hv'

/-- Cochrane (2023), eqs. (5.17)–(5.21), pp. 127–128, in a probability model: the model with
long-term debt — (5.1)–(5.2), the flow with the bond return `r^n`, the expectations hypothesis
`E_t r^n_{t+1} = i_t` and the returns `r^n_{t+1} = ω̃ q_{t+1} − q_t` (a.e.), with adapted
`x, π, v, q` and bounded `x, π, q`. -/
def MLTD (σ β κ ρ om : ℝ) (i s : ℕ → Ω → ℝ) (vm1 qm1 : Ω → ℝ) (x p v q rn : ℕ → Ω → ℝ) :
    Prop :=
  MNK S σ β κ i x p ∧ (∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + rn (t + 1) - p (t + 1) - s (t + 1)) ∧
  ρ • v 0 =ᵐ[S.μ] vm1 + rn 0 - p 0 - s 0 ∧ (∀ t, S.E t (rn (t + 1)) =ᵐ[S.μ] i t) ∧
  (∀ t, rn (t + 1) = om • q (t + 1) - q t) ∧ rn 0 = om • q 0 - qm1 ∧
  StronglyAdapted S.𝓕 x ∧ StronglyAdapted S.𝓕 p ∧ StronglyAdapted S.𝓕 v ∧
  StronglyAdapted S.𝓕 q ∧ S.BddProc x ∧ S.BddProc p ∧ S.BddProc q

/-- Cochrane (2023), pp. 127–128, in a probability model: the long-term-debt model is the general
model with forcing `e = s̃ − r^n` and `b_0 = v_{−1}`, plus the bond equations. -/
theorem mltd_eqm {σ β κ ρ om : ℝ} {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    {x p v q rn : ℕ → Ω → ℝ} (h : MLTD S σ β κ ρ om i s vm1 qm1 x p v q rn) :
    MEqm S σ β κ ρ i (fun t => s t - rn t) vm1 x p v := by
  obtain ⟨h1, hfl, h0, -, -, -, hxa, hpa, hva, -, hxb, hpb, -⟩ := h
  refine ⟨h1, fun t => ?_, ?_, hxa, hpa, hva, hxb, hpb⟩
  · filter_upwards [hfl t] with ω e1
    simp only [Pi.sub_apply, Pi.add_apply] at e1 ⊢
    rw [e1]
    ring
  · filter_upwards [h0] with ω e1
    simp only [Pi.sub_apply, Pi.add_apply] at e1 ⊢
    rw [e1]
    ring

/-- Cochrane (2023), eqs. (5.20)–(5.21), p. 128, **in a probability model**: for `|ω̃| < 1` and
bounded adapted `i`, a bounded adapted bond price is the forward solution
`q_t = −∑_k ω̃ᵏ E_t i_{t+k}` (a.e.). -/
theorem mbond_price {om : ℝ} (hom : |om| < 1) {i q rn : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i) (hqa : StronglyAdapted S.𝓕 q)
    (hqb : S.BddProc q) (h20 : ∀ t, S.E t (rn (t + 1)) =ᵐ[S.μ] i t)
    (h21 : ∀ t, rn (t + 1) = om • q (t + 1) - q t) :
    ∀ t, q t =ᵐ[S.μ] S.forwardSol om (-i) t := by
  obtain ⟨Mi, hMi⟩ := hib
  have hib' : ∀ t, ∀ᵐ ω ∂S.μ, |(-i) t ω| ≤ Mi := fun t => by
    filter_upwards [hMi t] with ω h
    simpa using h
  have hia' : StronglyAdapted S.𝓕 (-i) := fun t => (hia t).neg
  have hqi := int_of S hqa hqb
  have hsol : S.Solves om (-i) q := by
    intro t
    filter_upwards [h20 t, S.E_sub ((hqi (t + 1)).smul om) (hqi t) t,
      S.E_smul om (q (t + 1)) t] with ω e1 e2 e3
    rw [h21 t, e2] at e1
    simp only [Pi.sub_apply] at e1
    rw [e3, E_self S hqa hqb t] at e1
    simp only [Pi.smul_apply, smul_eq_mul] at e1
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linarith
  exact S.forward_unique hom hsol (S.forwardSol_solves hom hia' hib')
    (fun t => ((hqa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => ((S.forwardSol_adapted om _ t).mono (S.𝓕.le t)).aestronglyMeasurable) hqb
    (S.forwardSol_bdd hom hib')

/-- Cochrane (2023), p. 128 ("one more explosive root"), **determinacy with long-term debt in a
probability model**: for `0 < ρ < 1`, `|ω̃| < 1`, bounded adapted `i`, `s̃` and bounded
`𝓕₀`-measurable pre-sample values `v_{−1}`, `q_{−1}`, the model (5.17)–(5.21) has an equilibrium
with bounded debt, and any two agree a.e. at every date (including bond prices and returns). -/
theorem mltd_determinate {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hom : |om| < 1) {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i) (hsa : StronglyAdapted S.𝓕 s)
    (hsb : S.BddProc s) (hv0 : StronglyMeasurable[S.𝓕 0] vm1) {Bv : ℝ}
    (hvb : ∀ᵐ ω ∂S.μ, |vm1 ω| ≤ Bv) (hq0 : StronglyMeasurable[S.𝓕 0] qm1) {Bq : ℝ}
    (hqb : ∀ᵐ ω ∂S.μ, |qm1 ω| ≤ Bq) :
    (∃ x p v q rn, MLTD S σ β κ ρ om i s vm1 qm1 x p v q rn ∧ S.BddProc v) ∧
      ∀ x p v q rn x' p' v' q' rn', MLTD S σ β κ ρ om i s vm1 qm1 x p v q rn → S.BddProc v →
        MLTD S σ β κ ρ om i s vm1 qm1 x' p' v' q' rn' → S.BddProc v' →
          ∀ t, x t =ᵐ[S.μ] x' t ∧ p t =ᵐ[S.μ] p' t ∧ v t =ᵐ[S.μ] v' t ∧
            q t =ᵐ[S.μ] q' t ∧ rn t =ᵐ[S.μ] rn' t := by
  obtain ⟨Mi, hMi⟩ := hib
  have hib' : ∀ t, ∀ᵐ ω ∂S.μ, |(-i) t ω| ≤ Mi := fun t => by
    filter_upwards [hMi t] with ω h
    simpa using h
  have hia' : StronglyAdapted S.𝓕 (-i) := fun t => (hia t).neg
  -- the returns implied by a price path agree when the prices do
  have hrn_congr : ∀ {q q' rn rn' : ℕ → Ω → ℝ}, (∀ t, q t =ᵐ[S.μ] q' t) →
      (∀ t, rn (t + 1) = om • q (t + 1) - q t) → rn 0 = om • q 0 - qm1 →
      (∀ t, rn' (t + 1) = om • q' (t + 1) - q' t) → rn' 0 = om • q' 0 - qm1 →
      ∀ t, rn t =ᵐ[S.μ] rn' t := by
    intro q q' rn rn' hq h1 h0 h1' h0' t
    cases t with
    | zero =>
      filter_upwards [hq 0] with ω e
      rw [h0, h0']
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e]
    | succ t =>
      filter_upwards [hq t, hq (t + 1)] with ω e1 e2
      rw [h1, h1']
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e1, e2]
  refine ⟨?_, fun x p v q rn x' p' v' q' rn' h hv h' hv' => ?_⟩
  · set q := S.forwardSol om (-i)
    have hqs := S.forwardSol_solves hom hia' hib'
    have hqa : StronglyAdapted S.𝓕 q := S.forwardSol_adapted _ _
    have hqbd : S.BddProc q := S.forwardSol_bdd hom hib'
    obtain ⟨MQ, hMQ⟩ := hqbd
    set rn := LongTermDebt.rnOf om q qm1
    have hrna : StronglyAdapted S.𝓕 rn := by
      intro t
      cases t with
      | zero => exact ((hqa 0).const_smul om).sub hq0
      | succ t => exact ((hqa (t + 1)).const_smul om).sub ((hqa t).mono (S.𝓕.mono (Nat.le_succ t)))
    have hrnb : S.BddProc rn := by
      refine ⟨|om| * MQ + (MQ + |Bq|), fun t => ?_⟩
      cases t with
      | zero =>
        filter_upwards [hMQ 0, hqb] with ω h1 h2
        change |om * q 0 ω - qm1 ω| ≤ _
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        · have : 0 ≤ MQ := (abs_nonneg _).trans h1
          linarith [le_abs_self Bq]
      | succ t =>
        filter_upwards [hMQ (t + 1), hMQ t] with ω h1 h2
        change |om * q (t + 1) ω - q t ω| ≤ _
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        · linarith [abs_nonneg Bq]
    obtain ⟨x, p, v, h, hvbd⟩ := meqm_exists S hσ hκ hβ hρ0 hρ1 hia ⟨Mi, hMi⟩
      (e := fun t => s t - rn t) (fun t => (hsa t).sub (hrna t)) (mbdd_sub S hsb hrnb) hv0 hvb
    obtain ⟨h1, hfl, h0, hxa, hpa, hva, hxb, hpb⟩ := h
    have hqi := int_of S hqa ⟨MQ, hMQ⟩
    refine ⟨x, p, v, q, rn, ⟨h1, fun t => ?_, ?_, fun t => ?_, fun t => rfl, rfl, hxa, hpa, hva,
      hqa, hxb, hpb, ⟨MQ, hMQ⟩⟩, hvbd⟩
    · filter_upwards [hfl t] with ω e1
      simp only [Pi.sub_apply, Pi.add_apply] at e1 ⊢
      rw [e1]
      ring
    · filter_upwards [h0] with ω e1
      simp only [Pi.sub_apply, Pi.add_apply] at e1 ⊢
      rw [e1]
      ring
    · filter_upwards [hqs t, S.E_sub ((hqi (t + 1)).smul om) (hqi t) t,
        S.E_smul om (q (t + 1)) t] with ω e1 e2 e3
      change S.E t (om • q (t + 1) - q t) ω = i t ω
      rw [e2, Pi.sub_apply, e3, E_self S hqa ⟨MQ, hMQ⟩ t]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at e1 ⊢
      linarith
  · have hq := mbond_price S hom hia ⟨Mi, hMi⟩ h.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.2
      h.2.2.2.1 h.2.2.2.2.1
    have hq' := mbond_price S hom hia ⟨Mi, hMi⟩ h'.2.2.2.2.2.2.2.2.2.1 h'.2.2.2.2.2.2.2.2.2.2.2.2
      h'.2.2.2.1 h'.2.2.2.2.1
    have hqq : ∀ t, q t =ᵐ[S.μ] q' t := fun t => (hq t).trans (hq' t).symm
    have hrr := hrn_congr hqq h.2.2.2.2.1 h.2.2.2.2.2.1 h'.2.2.2.2.1 h'.2.2.2.2.2.1
    have he : ∀ t, (fun t => s t - rn' t) t =ᵐ[S.μ] (fun t => s t - rn t) t := fun t => by
      filter_upwards [hrr t] with ω e
      simp only [Pi.sub_apply, e]
    have hu := meqm_unique S hσ hκ hβ hρ0 hρ1 (mltd_eqm S h)
      (meqm_congr S (mltd_eqm S h') he) hv hv'
    exact fun t => ⟨(hu t).1, (hu t).2.1, (hu t).2.2, hqq t, hrr t⟩

/-! ### §5.1.1: all bounded equilibria of (5.1)–(5.2) -/

/-- Cochrane (2023), §5.1.1, eqs. (5.5)–(5.7), pp. 119–121, **the characterisation of all bounded
equilibria in a probability model**: for bounded adapted `i` and bounded adapted `(x, π)`,
(5.1)–(5.2) hold a.e. iff `x = F + gπ` a.e., where `F = E_t ∑ λ_U^{−k}(−σ/λ_U) i_{t+k}` is the
forward-solved rate term, and `E_t π_{t+1} = λ_S π_t − (κ/β) F_t` a.e. Inflation is therefore
pinned down only up to its initial value and its unexpected part `π_{t+1} − E_t π_{t+1}` (an
arbitrary bounded martingale difference). -/
theorem mnk_characterization {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i x p : ℕ → Ω → ℝ} (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i)
    (hxa : StronglyAdapted S.𝓕 x) (hpa : StronglyAdapted S.𝓕 p) (hxb : S.BddProc x)
    (hpb : S.BddProc p) :
    MNK S σ β κ i x p ↔
      (∀ t, x t =ᵐ[S.μ] S.forwardSol (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t) t +
          gainOf (nkP σ β κ) (lS σ β κ) • p t) ∧
        ∀ t, S.E t (p (t + 1)) =ᵐ[S.μ] lS σ β κ • p t - (κ / β) •
          S.forwardSol (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t) t := by
  obtain ⟨hsum, hprod, hU, -, -⟩ := roots_nk hσ hκ hβ
  have hβ' : (nkP σ β κ).beta ≠ 0 := by simpa [nkP] using hβ.ne'
  have hκ' : (nkP σ β κ).kappa ≠ 0 := by simpa [nkP] using hκ.ne'
  have hU0 : lU σ β κ ≠ 0 := by linarith
  have hinv : |(lU σ β κ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lU σ β κ)]
    exact inv_lt_one_of_one_lt₀ hU
  set G := gainOf (nkP σ β κ) (lS σ β κ)
  set F := S.forwardSol (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t)
  obtain ⟨Mi, hMi⟩ := hib
  have hib' : ∀ t, ∀ᵐ ω ∂S.μ, |((fun t => (-(σ / lU σ β κ)) • i t) t) ω| ≤
      |σ / lU σ β κ| * Mi := fun t => by
    filter_upwards [hMi t] with ω h
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hia' : StronglyAdapted S.𝓕 (fun t => (-(σ / lU σ β κ)) • i t) :=
    fun t => (hia t).const_smul _
  have hFs := S.forwardSol_solves hinv hia' hib'
  have hFa : StronglyAdapted S.𝓕 F := S.forwardSol_adapted _ _
  have hFb : S.BddProc F := S.forwardSol_bdd hinv hib'
  constructor
  · intro h
    obtain ⟨hf, hEp⟩ := mnk_props S hσ hκ hβ h hxa hpa hxb hpb
    have hff := S.forward_unique hinv hf hFs
      (fun t => ((fwd_adapted S hxa hpa t).mono (S.𝓕.le t)).aestronglyMeasurable)
      (fun t => ((hFa t).mono (S.𝓕.le t)).aestronglyMeasurable) (fwd_bdd S hxb hpb) hFb
    refine ⟨fun t => ?_, fun t => ?_⟩
    · filter_upwards [hff t] with ω e
      simp only [fwd, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e ⊢
      linarith
    · filter_upwards [hEp t, hff t] with ω e1 e2
      rw [e1]
      simp only [fwd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 ⊢
      rw [e2]
  · rintro ⟨hx, hEp⟩
    have hFi := int_of S hFa hFb
    have hpi := int_of S hpa hpb
    have hEF : ∀ t, ∀ᵐ ω ∂S.μ, S.E t (F (t + 1)) ω = lU σ β κ * F t ω + σ * i t ω := by
      intro t
      filter_upwards [hFs t] with ω hq
      have h2 : F t ω = (lU σ β κ)⁻¹ * S.E t (F (t + 1)) ω + -(σ / lU σ β κ) * i t ω := hq
      rw [h2]
      field_simp
      ring
    have hEx : ∀ t, S.E t (x (t + 1)) =ᵐ[S.μ] S.E t (F (t + 1) + G • p (t + 1)) :=
      fun t => S.E_congr (hx (t + 1)) t
    refine ⟨fun t => ?_, fun t => ?_⟩
    · filter_upwards [hx t, hEx t, E_add_smul S (hFi (t + 1)) (hpi (t + 1)) G t, hEF t, hEp t]
        with ω e0 e1 e2 e3 e4
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e0 e4 ⊢
      rw [e0, e1, e2, e3, e4]
      have := (blk_exist_pt (P := nkP σ β κ) hβ' hκ' hsum hprod (F := F t ω) (Pp := p t ω)
        (U := i t ω) rfl rfl).1
      have q1 : (nkP σ β κ).thIpi = 0 := rfl
      have q2 : (nkP σ β κ).thIx = 0 := rfl
      have q3 : (nkP σ β κ).sigma = σ := rfl
      have q4 : (nkP σ β κ).kappa = κ := rfl
      have q5 : (nkP σ β κ).beta = β := rfl
      rw [q1, q2, q3, q4, q5] at this
      simp only [zero_mul, zero_add] at this
      linarith
    · filter_upwards [hx t, hEp t] with ω e0 e1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
      rw [e0, e1]
      exact (blk_exist_pt (P := nkP σ β κ) hβ' hκ' hsum hprod (F := F t ω) (Pp := p t ω)
        (U := i t ω) rfl rfl).2

/-- Cochrane (2023), eq. (5.5), p. 119, **the moving-average form in a probability model**: in
every bounded adapted equilibrium of (5.1)–(5.2), with `F` the forward-solved rate term and
`δ_{k+1} = ΔE_{k+1} π_{k+1}` the unexpected inflation (a martingale difference), a.e.
`π_t = λ_Sᵗ π_0 + ∑_{k<t} λ_S^{t−1−k}(−(κ/β) F_k + δ_{k+1})`. -/
theorem mnk_ma {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i x p : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i) (hxa : StronglyAdapted S.𝓕 x)
    (hpa : StronglyAdapted S.𝓕 p) (hxb : S.BddProc x) (hpb : S.BddProc p)
    (h : MNK S σ β κ i x p) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, p t ω = lS σ β κ ^ t * p 0 ω + ∑ k ∈ Finset.range t, lS σ β κ ^ (t - 1 - k) *
      (-(κ / β) * S.forwardSol (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t) k ω +
        S.innov k (p (k + 1)) ω) := by
  obtain ⟨-, hEp⟩ := (mnk_characterization S hσ hκ hβ hia hib hxa hpa hxb hpb).1 h
  set F := S.forwardSol (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t)
  set l := lS σ β κ
  have hstep : ∀ k, ∀ᵐ ω ∂S.μ, p (k + 1) ω = l * p k ω + (-(κ / β) * F k ω +
      S.innov k (p (k + 1)) ω) := by
    intro k
    filter_upwards [hEp k] with ω e
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, E_self S hpa hpb (k + 1), e,
      Pi.smul_apply, smul_eq_mul]
    ring
  induction t with
  | zero => exact Eventually.of_forall fun ω => by simp
  | succ t ih =>
    filter_upwards [ih, hstep t] with ω e1 e2
    rw [e2, e1, Finset.sum_range_succ, mul_add, Finset.mul_sum]
    have h0 : t + 1 - 1 - t = 0 := by omega
    rw [h0, pow_zero, one_mul]
    have hs : ∑ k ∈ Finset.range t, l * (l ^ (t - 1 - k) * (-(κ / β) * F k ω +
        S.innov k (p (k + 1)) ω)) = ∑ k ∈ Finset.range t, l ^ (t + 1 - 1 - k) *
        (-(κ / β) * F k ω + S.innov k (p (k + 1)) ω) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k < t := Finset.mem_range.1 hk
      rw [show t + 1 - 1 - k = (t - 1 - k) + 1 by omega, pow_succ]
      ring
    rw [hs, pow_succ]
    ring

end Cochrane.StickyPriceFiscal.TidyR6MeasFiscalNK
