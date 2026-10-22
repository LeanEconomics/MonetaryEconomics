/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyIFT
import StabilizationWelfare.NonlinearNKMarkovRamseyMarkov

/-!
# The Markov representation of the timeless Rotemberg Ramsey equilibrium on a finite chain

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the optimal plan as a time-invariant
function of the predetermined multiplier and the exogenous state) and Appendix A.3, for the exact
Rotemberg Ramsey conditions. The event tree of a finite chain is
`NonlinearNKMarkovRamseyMarkov.chainTree` (reused from the Calvo modules).

* `Qd_congr`: the current Ramsey conditions depend on the lag only through `λ̂_{t−1}` — unlike
  Calvo, there is no predetermined price dispersion.
* **`ramsey_markov`**: if `G > 0`, there are `r, δ > 0` such that for every finite Markov chain and
  every disturbance pattern with `‖ξ‖ ≤ δ` there is ONE policy function `G : ℝ⁵ × S → ℝ⁵`,
  depending on the lag only through `λ̂_{t−1}`, with `z(x) = G(lag z(x), s(x))` at every node for
  every initial multiplier `‖d₀‖ ≤ δ`: the Markov representation in `(λ_{t−1}, s_t)`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyMarkov

open Filter Topology
open NonlinearNKMarkov (Mv)
open NonlinearNKMarkovRamseyTree (LagTree)
open NonlinearNKMarkovRamseyMarkov (lastS chainM chainTree lastS_append)
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyIFT

variable {S : Type*}

/-- Woodford (2003), Ch. 7: the current Ramsey conditions depend on the lag only through the
lagged multiplier `λ̂_{t−1}` (component 3). -/
theorem Qd_congr {p : Par} (e : Fin 3 → ℝ) {a a' : Fin 5 → ℝ} (u : Fin 5 → ℝ) (h3 : a 3 = a' 3) :
    Qd p (e, a, u) = Qd p (e, a', u) := by
  simp only [Qd, Qr, Pi.add_apply, h3]

/-- The projection on the predetermined multiplier `λ̂_{t−1}`. -/
def proj (d : Fin 5 → ℝ) : Fin 5 → ℝ := ![0, 0, 0, d 3, 0]

/-- The projection does not increase the sup norm. -/
theorem norm_proj_le (d : Fin 5 → ℝ) : ‖proj d‖ ≤ ‖d‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg d)).2 fun i => ?_
  fin_cases i <;> simp only [proj, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
    Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, norm_zero] <;>
    first | positivity | exact norm_le_pi_norm d _

/-- The residual on the chain tree, written out. -/
theorem PhiR_chain [Fintype S] {p : Par} (P : S → S → ℝ) (hP0 : ∀ s s', 0 ≤ P s s')
    (hP1 : ∀ s, ∑ s', P s s' = 1) (e : S × List S → Fin 3 → ℝ) (d w : S × List S → Fin 5 → ℝ)
    (x : S × List S) :
    PhiR (chainTree P hP0 hP1) p e d w x =
      Qd p (e x, (if x.2.length = 0 then d x else w (x.1, x.2.dropLast)), w x) +
        ∑ s', P (lastS x) s' • Nd p (w (x.1, x.2 ++ [s'])) := by
  funext i
  simp [PhiR, lagI, chainTree, chainM, Mv, Finset.sum_apply]

/-- Woodford (2003), Ch. 7, §1–2 and App. A.3 (**the MARKOV REPRESENTATION of the timeless
Ramsey equilibrium**): if `G > 0` (`0 < Gw p`), there are `r, δ > 0` such that for every finite
Markov chain and every disturbance pattern `ξ(s)` with `‖ξ‖ ≤ δ` there is ONE function
`G : ℝ⁵ × S → ℝ⁵`, depending on its first argument only through component 3 (the multiplier
`λ̂`), such that for every predetermined initial value `d₀` with `‖d₀‖ ≤ δ` the Ramsey equilibrium
`z` (unique within `r`) is `z(x) = G(lag z(x), s(x))` at every node: the plan is a
time-invariant function of `(λ̂_{t−1}, s_t)`. -/
theorem ramsey_markov {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ r > 0, ∃ δ > 0, ∀ (S : Type*) [Fintype S] (P : S → S → ℝ) (hP0 : ∀ s s', 0 ≤ P s s')
      (hP1 : ∀ s, ∑ s', P s s' = 1) (ξ : S → Fin 3 → ℝ), (∀ s, ‖ξ s‖ ≤ δ) →
        ∃ G : (Fin 5 → ℝ) → S → Fin 5 → ℝ,
          (∀ d d', d 3 = d' 3 → G d = G d') ∧
          ∀ d0 : Fin 5 → ℝ, ‖d0‖ ≤ δ → ∃ z : S × List S → Fin 5 → ℝ,
            ((∀ x, ‖z x‖ ≤ r) ∧
              PhiR (chainTree P hP0 hP1) p (fun x => ξ (lastS x)) (fun _ => d0) z = 0) ∧
            (∀ z' : S × List S → Fin 5 → ℝ, (∀ x, ‖z' x‖ ≤ r) →
              PhiR (chainTree P hP0 hP1) p (fun x => ξ (lastS x)) (fun _ => d0) z' = 0 →
                z' = z) ∧
            ∀ x, z x = G (lagI (chainTree P hP0 hP1) z (fun _ => d0) x) (lastS x) := by
  classical
  obtain ⟨r, hr, δ0, hδ0, C, hC, hex⟩ := ramsey_existence hp hG
  set τ' := δ0 / C with hτ'
  have hτ'0 : 0 < τ' := by positivity
  obtain ⟨ρc, hρc, hQc⟩ := Metric.continuousAt_iff.1
    ((contDiff_Qd (n := 0) p).continuous.continuousAt (x := 0)) τ' hτ'0
  refine ⟨r, hr, min δ0 (ρc / 2), lt_min hδ0 (by positivity),
    fun S _ P hP0 hP1 ξ hξ => ?_⟩
  set T := chainTree P hP0 hP1 with hT
  set e : S × List S → Fin 3 → ℝ := fun x => ξ (lastS x) with he
  have heδ : ∀ x, ‖e x‖ ≤ δ0 := fun x => (hξ _).trans (min_le_left _ _)
  have hW := fun (d : Fin 5 → ℝ) (hd : ‖d‖ ≤ δ0) => hex T e (fun _ => d) heδ (fun _ => hd)
  set Gc : (Fin 5 → ℝ) → S → Fin 5 → ℝ := fun q s =>
    if h : ‖q‖ ≤ δ0 then Classical.choose (hW q h) (s, []) else 0 with hGc
  refine ⟨fun d => Gc (proj d), fun d d' h3 => ?_, fun d0 hd0 => ?_⟩
  · have : proj d = proj d' := by funext i; fin_cases i <;> simp [proj, h3]
    simp only [this]
  have hd0' : ‖d0‖ ≤ δ0 := hd0.trans (min_le_left _ _)
  obtain ⟨z, ⟨hzB, hz⟩, hzu, hzs⟩ := hW d0 hd0'
  refine ⟨z, ⟨hzB, hz⟩, hzu, fun x0 => ?_⟩
  -- the equilibrium is small
  have hz0 : ∀ y, ‖PhiR T p e (fun _ => d0) (fun _ => 0) y‖ ≤ τ' := fun y => by
    have hss := Qd_Nd_zero hp
    have e1 : PhiR T p e (fun _ => d0) (fun _ => 0) y =
        Qd p (e y, lagI T (fun _ => 0) (fun _ => d0) y, 0) - Qd p 0 := by
      simp only [PhiR, Mv_const']
      rw [eq_neg_of_add_eq_zero_right hss]
      abel
    rw [e1, ← dist_eq_norm]
    refine (hQc ?_).le
    rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
    have hl : ‖lagI T (fun _ => (0 : Fin 5 → ℝ)) (fun _ => d0) y‖ ≤ ρc / 2 := by
      unfold lagI; split_ifs
      · exact hd0.trans (min_le_right _ _)
      · rw [norm_zero]; positivity
    have h0 : ‖(0 : Fin 5 → ℝ)‖ ≤ ρc / 2 := by rw [norm_zero]; positivity
    exact lt_of_le_of_lt (max_le ((hξ _).trans (min_le_right _ _)) (max_le hl h0))
      (by linarith)
  have hzδ : ∀ y, ‖z y‖ ≤ δ0 := fun y => (hzs τ' hτ'0.le hz0 y).trans
    (le_of_eq (by rw [hτ']; field_simp))
  -- the shifted process
  set dstar := lagI T z (fun _ => d0) x0 with hdstar
  have hdstarB : ‖proj dstar‖ ≤ δ0 := by
    refine (norm_proj_le _).trans ?_
    rw [hdstar]; unfold lagI; split_ifs
    · exact hd0'
    · exact hzδ _
  set sstar := lastS x0 with hsstar
  set W := Classical.choose (hW (proj dstar) hdstarB) with hWdef
  obtain ⟨⟨hWB, hWE⟩, hWu, -⟩ := Classical.choose_spec (hW (proj dstar) hdstarB)
  rw [← hWdef] at hWB hWE hWu
  set w' : S × List S → Fin 5 → ℝ := fun y =>
    if y.1 = sstar then z (x0.1, x0.2 ++ y.2) else W y with hw'
  have hw'B : ∀ y, ‖w' y‖ ≤ r := fun y => by
    simp only [hw']; split_ifs
    · exact hzB _
    · exact hWB _
  have hw'E : PhiR T p e (fun _ => proj dstar) w' = 0 := by
    funext y
    rw [PhiR_chain]
    by_cases hy : y.1 = sstar
    · have hz' := congrFun hz (x0.1, x0.2 ++ y.2)
      rw [PhiR_chain] at hz'
      simp only [Pi.zero_apply] at hz' ⊢
      rw [← hz']
      have hlast : lastS y = lastS (x0.1, x0.2 ++ y.2) := by
        rw [lastS_append, ← hsstar, ← hy]
      have hcur : w' y = z (x0.1, x0.2 ++ y.2) := by simp [hw', hy]
      have hch : ∀ s', w' (y.1, y.2 ++ [s']) = z (x0.1, x0.2 ++ y.2 ++ [s']) := fun s' => by
        simp [hw', hy, List.append_assoc]
      simp only [he, hlast, hcur, hch]
      congr 1
      by_cases hl : y.2 = []
      · have h1 : (x0.2 ++ y.2).length = 0 ↔ x0.2.length = 0 := by simp [hl]
        simp only [hl, List.length_nil, ↓reduceIte, List.append_nil]
        apply Qd_congr
        simp only [hdstar, proj, lagI, T, chainTree]
        split_ifs <;> simp
      · have h1 : (x0.2 ++ y.2).length ≠ 0 := by simp [hl]
        have h2 : y.2.length ≠ 0 := by simpa using hl
        simp only [h1, h2, ↓reduceIte]
        have h3 : w' (y.1, y.2.dropLast) = z (x0.1, (x0.2 ++ y.2).dropLast) := by
          simp [hw', hy, List.dropLast_append_of_ne_nil hl]
        rw [h3]
    · have hW' := congrFun hWE y
      rw [PhiR_chain] at hW'
      simp only [Pi.zero_apply] at hW' ⊢
      rw [← hW']
      have hcur : w' y = W y := by simp [hw', hy]
      have hch : ∀ s', w' (y.1, y.2 ++ [s']) = W (y.1, y.2 ++ [s']) := fun s' => by
        simp [hw', hy]
      have hpar : w' (y.1, y.2.dropLast) = W (y.1, y.2.dropLast) := by simp [hw', hy]
      simp only [hcur, hch, hpar]
  have hw'W := hWu w' hw'B hw'E
  have := congrFun hw'W (sstar, [])
  simp only [hw', ↓reduceIte, List.append_nil] at this
  rw [this]
  simp only [hGc, hdstarB, ↓reduceDIte]
  rw [← hWdef]

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyMarkov
