/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasFiscalNK

/-!
# The responses of §5.1.2 in a probability model: forecasts are perfect-foresight paths

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1.2, pp. 121–125, with
Figs. 5.1 and 5.3 (the responses to an unexpected permanent rate rise and to a fiscal shock).

The book draws its responses as perfect-foresight paths after an unexpected shock. In a genuine
probability model the response is the **revision of forecasts**, `E_1 π_{1+j} − E_0 π_{1+j}`.
This module proves the bridge: in every bounded equilibrium of the measure-theoretic model
`TidyR6MeasFiscalNK.MFTPLNK`, for every forecast date `s` and almost every state `ω`, the
forecast paths `k ↦ E_s x_{s+k}(ω)`, `E_s π_{s+k}(ω)`, `E_s v_{s+k}(ω)` form a **perfect-foresight
equilibrium** (the core `FiscalNK.FTPLNK` under `perfectForesight`) driven by the forecast paths of
the rate and the surplus, from the date-`s` debt `b̂_s` (`pf_forecast`, `bHat_zero`,
`bHat_succ`). Every closed form of `FiscalNK` therefore applies state by state.

## Main results

* **`pf_forecast`**: the bridge (certainty equivalence of forecasts in the linear model).
* **`forecast_closed_form`**: if the date-`s` forecasts of the rate are a constant `a(ω)` and of the
  surplus a bounded path `s̃(ω)`, then a.e. `E_s π_{s+k} = a + (1 − ρ/λ₁)(b̂ − a − S)λ₁^{−k}`
  (`FiscalNK.piDet`), and likewise output and debt.
* **`fig51_response`** (Fig. 5.1 as forecast revisions): with a date-1 rate shock `ε`
  (`E_0 ε = 0`), `i_t = ε` for `t ≥ 1`, `E_0 π_{1+j} = 0` and
  `E_1 π_{1+j} = ε (1 − (1 − ρ/λ₁) λ₁^{−j})` a.e.
* **`fig53_response`** (Fig. 5.3): with a date-1 fiscal shock `ε` scaling a surplus path of present
  value `−1`, `E_0 π_{1+j} = 0` and `E_1 π_{1+j} = ε (1 − ρ/λ₁) λ₁^{−j}` a.e.
* §5.3 in a probability model: `fig51_fisherian` (the revision tends to the new rate `ε`: the
  Fisherian long run), `fig51_impact` (with one-period debt the impact revision is `ε ρ/λ₁`, of
  the sign of the rise: no impact disinflation).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasResponses

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRulesMeasure NKModel FiscalNK
  TidyR6MeasFiscalNK

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), p. 121 (the predetermined debt of a forecast path): `b̂_s = ρ E_s v_s +
E_s π_s + E_s s̃_s`, which is `b₀` at `s = 0` and `v_{s−1} + i_{s−1}` afterwards. -/
noncomputable def bHat (ρ : ℝ) (s v p : ℕ → Ω → ℝ) (s0 : ℕ) (ω : Ω) : ℝ :=
  ρ * S.E s0 (v s0) ω + S.E s0 (p s0) ω + S.E s0 (s s0) ω

/-- Cochrane (2023), pp. 121–125, **the forecast paths are perfect-foresight equilibria**: in a
bounded equilibrium of (5.15)–(5.16) with bounded adapted `i`, `s̃`, for every date `s` and almost
every state `ω`, `k ↦ (E_s x_{s+k}, E_s π_{s+k}, E_s v_{s+k})(ω)` is a bounded equilibrium of the
perfect-foresight model driven by `k ↦ E_s i_{s+k}(ω)`, `E_s s̃_{s+k}(ω)` from `b̂_s(ω)`. -/
theorem pf_forecast {σ β κ ρ : ℝ} {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ i s b0 x p v) (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i)
    (hsa : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s) (hvb : S.BddProc v) (s0 : ℕ) :
    ∀ᵐ ω ∂S.μ, FTPLNK perfectForesight σ β κ ρ (fun k _ => S.E s0 (i (s0 + k)) ω)
        (fun k _ => S.E s0 (s (s0 + k)) ω) (fun _ => bHat S ρ s v p s0 ω)
        (fun k _ => S.E s0 (x (s0 + k)) ω) (fun k _ => S.E s0 (p (s0 + k)) ω)
        (fun k _ => S.E s0 (v (s0 + k)) ω) ∧
      BoundedProc (fun k (_ : Unit) => S.E s0 (p (s0 + k)) ω) ∧
      BoundedProc (fun k (_ : Unit) => S.E s0 (v (s0 + k)) ω) := by
  obtain ⟨⟨his, hpc⟩, hfl, -, hxa, hpa, hva, hxb, hpb⟩ := h
  have hxi := int_of S hxa hxb
  have hpi := int_of S hpa hpb
  have hii := int_of S hia hib
  have hsi := int_of S hsa hsb
  have hvi := int_of S hva hvb
  -- IS forecasts
  have hIS : ∀ k, ∀ᵐ ω ∂S.μ, S.E s0 (x (s0 + k)) ω = S.E s0 (x (s0 + k + 1)) ω -
      σ * (S.E s0 (i (s0 + k)) ω - S.E s0 (p (s0 + k + 1)) ω) := by
    intro k
    have hA := S.integrable_E (s0 + k) (x (s0 + k + 1))
    have hC := S.integrable_E (s0 + k) (p (s0 + k + 1))
    filter_upwards [S.E_congr (his (s0 + k)) s0,
      E_sub_smul S hA ((hii (s0 + k)).sub hC) σ s0, S.E_sub (hii (s0 + k)) hC s0,
      S.E_tower (Nat.le_add_right s0 k) (x (s0 + k + 1)),
      S.E_tower (Nat.le_add_right s0 k) (p (s0 + k + 1))] with ω e2 e3 e4 e5 e6
    rw [e2, e3, e4, Pi.sub_apply, e5, e6]
  have hPC : ∀ k, ∀ᵐ ω ∂S.μ, S.E s0 (p (s0 + k)) ω = β * S.E s0 (p (s0 + k + 1)) ω +
      κ * S.E s0 (x (s0 + k)) ω := by
    intro k
    have hC := S.integrable_E (s0 + k) (p (s0 + k + 1))
    filter_upwards [S.E_congr (hpc (s0 + k)) s0, E_comb S hC (hxi (s0 + k)) β κ s0,
      S.E_tower (Nat.le_add_right s0 k) (p (s0 + k + 1))] with ω e1 e2 e3
    rw [e1, e2, e3]
  have hFL : ∀ k, ∀ᵐ ω ∂S.μ, ρ * S.E s0 (v (s0 + k + 1)) ω = S.E s0 (v (s0 + k)) ω +
      S.E s0 (i (s0 + k)) ω - S.E s0 (p (s0 + k + 1)) ω - S.E s0 (s (s0 + k + 1)) ω := by
    intro k
    filter_upwards [S.E_congr (hfl (s0 + k)) s0, S.E_smul ρ (v (s0 + k + 1)) s0,
      S.E_sub (((hvi (s0 + k)).add (hii (s0 + k))).sub (hpi (s0 + k + 1))) (hsi (s0 + k + 1)) s0,
      S.E_sub ((hvi (s0 + k)).add (hii (s0 + k))) (hpi (s0 + k + 1)) s0,
      S.E_add (hvi (s0 + k)) (hii (s0 + k)) s0] with ω e1 e2 e3 e4 e5
    rw [e2] at e1
    simp only [Pi.smul_apply, smul_eq_mul] at e1
    rw [e1, e3, Pi.sub_apply, e4, Pi.sub_apply, e5, Pi.add_apply]
  obtain ⟨Mp, hMp⟩ := hpb
  obtain ⟨Mv, hMv⟩ := hvb
  filter_upwards [ae_all_iff.2 hIS, ae_all_iff.2 hPC, ae_all_iff.2 hFL,
    ae_all_iff.2 fun k => S.abs_E_le (hMp (s0 + k)) s0,
    ae_all_iff.2 fun k => S.abs_E_le (hMv (s0 + k)) s0] with ω e1 e2 e3 e4 e5
  refine ⟨⟨⟨fun k => ?_, fun k => ?_⟩, fun k => ?_, ?_⟩, ⟨Mp, fun k _ => e4 k⟩,
    ⟨Mv, fun k _ => e5 k⟩⟩
  · funext u
    change S.E s0 (x (s0 + k)) ω = S.E s0 (x (s0 + (k + 1))) ω -
      σ * (S.E s0 (i (s0 + k)) ω - S.E s0 (p (s0 + (k + 1))) ω)
    exact e1 k
  · funext u
    change S.E s0 (p (s0 + k)) ω = β * S.E s0 (p (s0 + (k + 1))) ω +
      κ * S.E s0 (x (s0 + k)) ω
    exact e2 k
  · funext u
    change ρ * S.E s0 (v (s0 + (k + 1))) ω = S.E s0 (v (s0 + k)) ω +
      S.E s0 (i (s0 + k)) ω - S.E s0 (p (s0 + (k + 1))) ω - S.E s0 (s (s0 + (k + 1))) ω
    exact e3 k
  · funext u
    change ρ * S.E s0 (v (s0 + 0)) ω = bHat S ρ s v p s0 ω - S.E s0 (p (s0 + 0)) ω -
      S.E s0 (s (s0 + 0)) ω
    simp only [bHat, add_zero]
    ring

/-- Cochrane (2023), p. 121: at `s = 0` the forecast path starts from the initial debt,
`b̂_0 = b_0` a.e. -/
theorem bHat_zero {σ β κ ρ : ℝ} {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ i s b0 x p v) (hsa : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hvb : S.BddProc v) : ∀ᵐ ω ∂S.μ, bHat S ρ s v p 0 ω = b0 ω := by
  obtain ⟨-, -, h0, -, hpa, hva, -, hpb⟩ := h
  filter_upwards [h0] with ω e
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e
  simp only [bHat, E_self S hva hvb 0, E_self S hpa hpb 0, E_self S hsa hsb 0]
  linarith

/-- Cochrane (2023), p. 121 (`b_{t+1} = v_t + i_t`, predetermined): at `s = t + 1` the forecast
path starts from `b̂_{t+1} = v_t + i_t` a.e. -/
theorem bHat_succ {σ β κ ρ : ℝ} {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ i s b0 x p v) (hsa : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s)
    (hvb : S.BddProc v) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, bHat S ρ s v p (t + 1) ω = v t ω + i t ω := by
  obtain ⟨-, hfl, -, -, hpa, hva, -, hpb⟩ := h
  filter_upwards [hfl t] with ω e
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e
  simp only [bHat, E_self S hva hvb (t + 1), E_self S hpa hpb (t + 1),
    E_self S hsa hsb (t + 1)]
  linarith

/-- Cochrane (2023), pp. 122–125, **closed-form forecasts**: if a.e. the date-`s` forecasts of the
rate are a constant `a(ω)` and of the surplus a bounded path `s̃(ω)`, then for
`0 < ρ < 1`, a.e., `E_s π_{s+k} = π^{det}_k(a, b̂_s, s̃)` (`FiscalNK.piDet`), and likewise output
(`FiscalNK.xDet`) and debt (`FiscalNK.vDet`). -/
theorem forecast_closed_form {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ i s b0 x p v) (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i)
    (hsa : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s) (hvb : S.BddProc v) (s0 : ℕ)
    (a : Ω → ℝ) (sv : Ω → ℕ → ℝ) (hsv : ∀ ω, ∃ M, ∀ k, |sv ω k| ≤ M)
    (hai : ∀ᵐ ω ∂S.μ, ∀ k, S.E s0 (i (s0 + k)) ω = a ω)
    (has : ∀ᵐ ω ∂S.μ, ∀ k, S.E s0 (s (s0 + k)) ω = sv ω k) :
    ∀ᵐ ω ∂S.μ, ∀ k,
      S.E s0 (p (s0 + k)) ω = piDet σ β κ ρ (a ω) (bHat S ρ s v p s0 ω) (sv ω) k ∧
      S.E s0 (x (s0 + k)) ω = xDet σ β κ ρ (a ω) (bHat S ρ s v p s0 ω) (sv ω) k ∧
      S.E s0 (v (s0 + k)) ω = vDet σ β κ ρ (a ω) (bHat S ρ s v p s0 ω) (sv ω) k := by
  filter_upwards [pf_forecast S h hia hib hsa hsb hvb s0, hai, has] with ω ⟨hpf, hpb, hvb'⟩ e1 e2
  have hi : (fun k (_ : Unit) => S.E s0 (i (s0 + k)) ω) = fun _ _ => a ω := by
    funext k u
    exact e1 k
  have hs : (fun k (_ : Unit) => S.E s0 (s (s0 + k)) ω) = fun k _ => sv ω k := by
    funext k u
    exact e2 k
  rw [hi, hs] at hpf
  obtain ⟨M, hM⟩ := hsv ω
  obtain ⟨hx, hp, hv⟩ := det_unique perfectForesight hσ hκ hβ hρ0 hρ1 (a ω)
    (bHat S ρ s v p s0 ω) hM hpf hpb hvb'
  intro k
  exact ⟨congrFun (congrFun hp k) (), congrFun (congrFun hx k) (), congrFun (congrFun hv k) ()⟩

/-- Cochrane (2023), Fig. 5.1, p. 122, **as forecast revisions in a probability model**: a date-1
rate shock `ε` (bounded, `𝓕₁`-measurable, `E_0 ε = 0`), the rate `i_0 = 0`, `i_t = ε` for
`t ≥ 1`, no surpluses, `b_0 = 0`. In every bounded equilibrium, a.e., `E_0 π_{1+j} = 0` and
`E_1 π_{1+j} = ε (1 − (1 − ρ/λ₁) λ₁^{−j})`: the response to the news is the book's path. -/
theorem fig51_response {σ β κ ρ B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ (fun t => if t = 0 then 0 else ε) 0 0 x p v) (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.E 0 (p (1 + j)) ω = 0 ∧
      S.E 1 (p (1 + j)) ω = ε ω * (1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ j) := by
  set i : ℕ → Ω → ℝ := fun t => if t = 0 then 0 else ε
  have hεi : Integrable ε S.μ :=
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable hεm hεb).integrable
  have hia : StronglyAdapted S.𝓕 i := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · simp only [i, ht, ↓reduceIte]
      exact stronglyMeasurable_const
    · simp only [i, ht.ne', ↓reduceIte]
      exact hεm.mono (S.𝓕.mono ht)
  have hib : S.BddProc i := ⟨|B|, fun t => by
    filter_upwards [hεb] with ω h1
    by_cases ht : t = 0
    · simp [i, ht]
    · simp only [i, ht, ↓reduceIte]
      exact h1.trans (le_abs_self B)⟩
  have hsa : StronglyAdapted S.𝓕 (0 : ℕ → Ω → ℝ) := fun t => stronglyMeasurable_const
  have hsb : S.BddProc (0 : ℕ → Ω → ℝ) := mbdd_zero S
  -- date-0 forecasts: zero rates, zero surpluses, `b̂_0 = 0`
  have h0 := forecast_closed_form S hσ hκ hβ hρ0 hρ1 h hia hib hsa hsb hvb 0
    (fun _ => 0) (fun _ _ => 0) (fun _ => ⟨0, fun _ => by simp⟩) (by
      filter_upwards [hε0] with ω e k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · simp only [zero_add, hk, i, ↓reduceIte]
        rw [S.E_zero]
        rfl
      · simp only [zero_add, i, hk.ne', ↓reduceIte]
        exact e) (Eventually.of_forall fun ω k => by simp [S.E_zero])
  have hb0 := bHat_zero S h hsa hsb hvb
  -- date-1 forecasts: the rate `ε`, zero surpluses, `b̂_1 = v_0 + i_0 = v_0`
  have h1 := forecast_closed_form S hσ hκ hβ hρ0 hρ1 h hia hib hsa hsb hvb 1
    ε (fun _ _ => 0) (fun _ => ⟨0, fun _ => by simp⟩) (Eventually.of_forall fun ω k => by
      simp only [show 1 + k ≠ 0 by omega, i, ↓reduceIte]
      rw [S.E_of_stronglyMeasurable hεm hεi]) (Eventually.of_forall fun ω k => by
        simp [S.E_zero])
  have hb1 := bHat_succ S h hsa hsb hvb 0
  -- `v_0 = 0`: the date-0 forecast of debt
  have hpv0 : ∀ᵐ ω ∂S.μ, v 0 ω = 0 := by
    filter_upwards [h0, hb0] with ω e1 e2
    have := (e1 0).2.2
    rw [E_self S h.2.2.2.2.2.1 hvb 0] at this
    rw [this, vDet, e2]
    simp [pvS]
  have hpvS : pvS ρ (fun _ : ℕ => (0 : ℝ)) = 0 := by simp [pvS]
  filter_upwards [h0, h1, hb0, hb1, hpv0] with ω e0 e1 eb0 eb1 ev0 j
  refine ⟨?_, ?_⟩
  · have := (e0 (1 + j)).1
    rw [zero_add] at this
    rw [this, piDet, eb0, hpvS]
    simp
  · rw [(e1 j).1, piDet, eb1, ev0, hpvS]
    simp only [i, ↓reduceIte, zero_add, Pi.zero_apply]
    ring

/-- Cochrane (2023), Fig. 5.3, p. 124, **as forecast revisions in a probability model**: a date-1
fiscal shock `ε` (bounded, `𝓕₁`-measurable, `E_0 ε = 0`) scales a deterministic bounded surplus
path `s̃` with present value `∑ ρʲ s̃_j = −1`: surpluses `s_0 = 0`, `s_{1+j} = ε s̃_j`, no rate
changes, `b_0 = 0`. In every bounded equilibrium, a.e., `E_0 π_{1+j} = 0` and
`E_1 π_{1+j} = ε (1 − ρ/λ₁) λ₁^{−j}`. -/
theorem fig53_response {σ β κ ρ B Ms : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {sv : ℕ → ℝ}
    (hsv : ∀ j, |sv j| ≤ Ms) (hpv : pvS ρ sv = -1) {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ 0 (fun t ω => if t = 0 then 0 else ε ω * sv (t - 1)) 0 x p v)
    (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.E 0 (p (1 + j)) ω = 0 ∧
      S.E 1 (p (1 + j)) ω = ε ω * ((1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ j) := by
  set s : ℕ → Ω → ℝ := fun t ω => if t = 0 then 0 else ε ω * sv (t - 1)
  have hεi : Integrable ε S.μ :=
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable hεm hεb).integrable
  have hsa : StronglyAdapted S.𝓕 s := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · simp only [s, ht, ↓reduceIte]
      exact stronglyMeasurable_const
    · simp only [s, ht.ne', ↓reduceIte]
      exact (hεm.mono (S.𝓕.mono ht)).mul stronglyMeasurable_const
  have hMs : 0 ≤ Ms := (abs_nonneg _).trans (hsv 0)
  have hsb : S.BddProc s := ⟨|B| * Ms, fun t => by
    filter_upwards [hεb] with ω h1
    by_cases ht : t = 0
    · simp only [s, ht, ↓reduceIte, abs_zero]
      positivity
    · simp only [s, ht, ↓reduceIte, abs_mul]
      exact mul_le_mul (h1.trans (le_abs_self B)) (hsv _) (abs_nonneg _) (abs_nonneg _)⟩
  have hia : StronglyAdapted S.𝓕 (0 : ℕ → Ω → ℝ) := fun t => stronglyMeasurable_const
  have hib : S.BddProc (0 : ℕ → Ω → ℝ) := mbdd_zero S
  have hEs : ∀ k, ∀ᵐ ω ∂S.μ, S.E 0 (s (0 + k)) ω = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · refine Eventually.of_forall fun ω => ?_
      simp only [zero_add, hk, s, ↓reduceIte]
      rw [S.E_const]
    · have hfun : s (0 + k) = (sv (k - 1)) • ε := by
        funext ω
        simp only [zero_add, s, hk.ne', ↓reduceIte, Pi.smul_apply, smul_eq_mul]
        ring
      filter_upwards [S.E_smul (sv (k - 1)) ε 0, hε0] with ω e1 e2
      rw [hfun, e1, Pi.smul_apply, e2, Pi.zero_apply, smul_zero]
  have h0 := forecast_closed_form S hσ hκ hβ hρ0 hρ1 h hia hib hsa hsb hvb 0
    (fun _ => 0) (fun _ _ => 0) (fun _ => ⟨0, fun _ => by simp⟩)
    (Eventually.of_forall fun ω k => by simp [S.E_zero]) (ae_all_iff.2 hEs)
  have hb0 := bHat_zero S h hsa hsb hvb
  have h1 := forecast_closed_form S hσ hκ hβ hρ0 hρ1 h hia hib hsa hsb hvb 1
    (fun _ => 0) (fun ω j => ε ω * sv j) (fun ω => ⟨|ε ω| * Ms, fun j => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hsv j) (abs_nonneg _)⟩)
    (Eventually.of_forall fun ω k => by simp [S.E_zero])
    (Eventually.of_forall fun ω k => by
      have hfun : s (1 + k) = fun ω => ε ω * sv k := by
        funext ω
        simp only [s, show 1 + k ≠ 0 by omega, ↓reduceIte, show 1 + k - 1 = k by omega]
      rw [hfun]
      exact congrFun (S.E_of_stronglyMeasurable (x := fun ω => ε ω * sv k)
        (hεm.mul stronglyMeasurable_const) (hεi.mul_const (sv k))) ω)
  have hb1 := bHat_succ S h hsa hsb hvb 0
  have hpv0 : ∀ᵐ ω ∂S.μ, v 0 ω = 0 := by
    filter_upwards [h0, hb0] with ω e1 e2
    have := (e1 0).2.2
    rw [E_self S h.2.2.2.2.2.1 hvb 0] at this
    rw [this, vDet, e2]
    simp [pvS]
  have hpvε : ∀ ω, pvS ρ (fun j => ε ω * sv j) = -ε ω := by
    intro ω
    rw [pvS, show (fun j => ρ ^ j * (ε ω * sv j)) = fun j => ε ω * (ρ ^ j * sv j) by
      funext j; ring, tsum_mul_left, ← pvS, hpv]
    ring
  have hpvS : pvS ρ (fun _ : ℕ => (0 : ℝ)) = 0 := by simp [pvS]
  filter_upwards [h0, h1, hb0, hb1, hpv0] with ω e0 e1 eb0 eb1 ev0 j
  refine ⟨?_, ?_⟩
  · have := (e0 (1 + j)).1
    rw [zero_add] at this
    rw [this, piDet, eb0, hpvS]
    simp
  · rw [(e1 j).1, piDet, eb1, ev0, hpvε]
    simp only [Pi.zero_apply]
    ring

/-- Cochrane (2023), §5.3, p. 132 ("the Fisherian long run"), **as forecast revisions in a
probability model**: after the date-1 rate shock of `fig51_response`, the revision of expected
inflation `E_1 π_{1+j} − E_0 π_{1+j}` converges a.e. to the new rate `ε` as `j → ∞`. -/
theorem fig51_fisherian {σ β κ ρ B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ (fun t => if t = 0 then 0 else ε) 0 0 x p v) (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, Tendsto (fun j => S.E 1 (p (1 + j)) ω - S.E 0 (p (1 + j)) ω) atTop (𝓝 (ε ω)) := by
  have hl1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  filter_upwards [fig51_response S hσ hκ hβ hρ0 hρ1 hεm hεb hε0 h hvb] with ω e
  simp_rw [fun j => (e j).1, fun j => (e j).2, sub_zero]
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul
    (1 - ρ * (lam1 σ β κ)⁻¹)).const_sub 1 |>.const_mul (ε ω)
  simpa using this

/-- Cochrane (2023), §5.3, p. 131 ("with one-period debt there is no impact disinflation"),
**as a forecast revision in a probability model**: after the date-1 rate shock of
`fig51_response`, the impact revision is `E_1 π_1 − E_0 π_1 = ε ρ/λ₁`, which has the sign of
the rate rise `ε`. -/
theorem fig51_impact {σ β κ ρ B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ (fun t => if t = 0 then 0 else ε) 0 0 x p v) (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, S.E 1 (p 1) ω - S.E 0 (p 1) ω = ε ω * (ρ * (lam1 σ β κ)⁻¹) ∧
      (0 < ε ω → 0 < S.E 1 (p 1) ω - S.E 0 (p 1) ω) := by
  have hl1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  filter_upwards [fig51_response S hσ hκ hβ hρ0 hρ1 hεm hεb hε0 h hvb] with ω e
  have e0 := e 0
  simp only [add_zero, pow_zero, mul_one] at e0
  have hval : S.E 1 (p 1) ω - S.E 0 (p 1) ω = ε ω * (ρ * (lam1 σ β κ)⁻¹) := by
    rw [e0.1, e0.2]
    ring
  refine ⟨hval, fun hε => ?_⟩
  rw [hval]
  have : 0 < (lam1 σ β κ)⁻¹ := inv_pos.mpr (by linarith)
  positivity

end Cochrane.StickyPriceFiscal.TidyR6MeasResponses
