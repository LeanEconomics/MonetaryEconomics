/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bGovRamseyAEZero
import StabilizationWelfare.TidyR6bGovRamseyAR1

/-!
# The Markov representation of the Ramsey equilibrium with purchases when `H = 0`

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (`s_C < 1`), Chapter 7, §1–2, Chapter 6,
§1, and Appendix A.3.

The construction of `TidyR6bGovRamseyAR1` for the case `H = A_uG − γ_G = 0`, with the inverse
of `TidyR6bGovRamseyZero` (restated from that module):

* `measV_LinvRZ`, `tree_solZ`.
* **`gov_ramsey_ar1_markov_zero`**: if `s_C > 0`, `H = 0` and `A_uG ≠ 0`, the adapted, a.s.
  unique solution of the TRUE Ramsey conditions with purchases is `z_t = G(z_{t−1}, x_t)` a.s.
  with ONE measurable `G`, depending on `z_{t−1}` only through `(Δ̂, λ̂₁, λ̂₂)`.
-/

namespace Woodford.StabilizationWelfare.TidyR6bGovRamseyAR1Zero

open MeasureTheory ProbabilityTheory Filter Topology
open NonlinearNKMarkov hiding M_lin
open NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT NonlinearNKMarkovAR1Markov
open NonlinearNKMarkovRamseyAR1 TidyR6bGovRamsey TidyR6bGovRamseyTree TidyR6bRamseyNewton
open TidyR6bGovRamseyZero TidyR6bGovRamseyAR1

variable {δ Bx : ℝ}

/-- Woodford (2003), App. A.3 (`H = 0`): the inverse of the linearised Ramsey operator preserves
measurability on the AR(1) tree (for bounded forcings). -/
theorem measV_LinvRZ (ν : ProbabilityMeasure ℝ) {p : Par} (R : RPar) (hp : p.Std) {γ : ℝ}
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0)
    {r : Node δ Bx → Fin 9 → ℝ} (hr : MeasV r) {A : ℝ} (hA : 0 ≤ A)
    (hrb : ∀ y k, |r y k| ≤ A) : MeasV (LinvRZ (arTree ν δ Bx) p R γ r) := by
  set T := arTree ν δ Bx
  have hc : ∀ k, MN (fun x => r x k) := fun k => mn_comp hr k
  obtain ⟨cy, -, by'⟩ := bd_yvZ R hp γ hH0 hAG
  obtain ⟨cπ, -, bπ⟩ := bd_pivZ R hp γ hH0 hAG
  have hD : MN (Dv T p r) := mn_bwd ν _ ((mn_lin2 (hc 7) (hc 8) (aE p / (p.θ - 1)) 1).congr
    fun x => by ring)
  have hM : MN (Muv T p R r) := mn_bwd ν _ ((mn_lin2 (mn_lin2 (hc 2) (hc 3) 1 1) (hc 7) 1
    (-(ramseyLam p R 0 * p.c0 / (p.θ - 1)))).congr fun x => by ring)
  have hr7M : MN (T.M fun y => r y 7) := mn_M ν (hc 7) (hrb · 7)
  have hg : MN (gv T p r) := (mn_lin2 (mn_lin2 (hc 6) (hc 5) 1 (-1)) (mn_lin2 (hc 7) hr7M 1
    (-(p.α * p.β))) ((1 - p.α) / (p.c0 * p.α)) (1 / (p.α * (p.θ - 1)))).congr fun x => by
      simp only [gv]; ring
  have hDl := mn_lag ν hD
  have hMl := mn_lag ν hM
  have hr0l := mn_lag ν (hc 0)
  have hFt : MN (Ftv T p R r) := by
    have e1 := mn_lin2 (mn_lin2 hMl hDl 1 (ramseyLam p R 3)) (hc 7)
      (-((1 - p.α) * aE p / p.c0)) (-((p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) /
        (p.θ - 1)))
    have e2 := mn_lin2 e1 (mn_lin2 (hc 2) (hc 1) 1 (-((1 - p.α) / (p.α * p.c0)))) 1 1
    have e3 := mn_lin2 (mn_lin2 (hc 0) hr0l 1 (-1)) (mn_lin2 hD hDl 1 (-1)) 1
      ((1 - R.Φ) * R.Au)
    have e4 := mn_lin2 e3 (mn_lin2 hM hMl 1 (-1)) 1 ((1 - p.α * p.β) * (1 + p.ω))
    exact (mn_lin2 e2 e4 ((1 - p.α * p.β) * (p.σ + p.ω)) (-1)).congr fun x => by
      simp only [Ftv]; ring
  have hπ : MN (pivZ T p R γ r) :=
    (mn_lin2 hFt hFt (1 / (R.Au * Gw p R * p.θ)) 0).congr fun x => by simp only [pivZ]; ring
  have hπM0 : MN (T.M (pivZ T p R γ r)) := mn_M ν hπ (bπ T r A hA hrb)
  have hy : MN (yvZ T p R γ r) := (mn_lin2 (mn_lin2 hπ hπM0 1 (-p.β)) hg (1 / p.κ)
    (-(1 / p.κ))).congr fun x => by simp only [yvZ]; ring
  have hπM : MN (T.M (pivZ T p R γ r)) := mn_M ν hπ (bπ T r A hA hrb)
  have hF : MN (FvZ T p R γ r) := by
    have hin := mn_lin2 (mn_lin2 hy hπM ((1 - p.α * p.β) * (1 - p.σ)) (p.α * p.β * (p.θ - 1)))
      (hc 5) 1 1
    have hb := lb2 (lb2 (by' T r A hA hrb) (lbM T (bπ T r A hA hrb))
      ((1 - p.α * p.β) * (1 - p.σ)) (p.α * p.β * (p.θ - 1))) (g := fun y => r y 5) (cg := 1)
      (fun y => by simpa using hrb y 5) 1 1
    exact (mn_fwdS ν (abs_ab hp) hin hb).congr fun x => by simp only [FvZ]; congr 1; funext y; ring
  have hx : MN (xvZ T p R γ r) := (mn_lin2 hπ (hc 7) (p.α * (p.θ - 1) / ((1 - p.α) * (p.θ - 1)))
    (-(1 / ((1 - p.α) * (p.θ - 1))))).congr fun x => by simp only [xvZ]; ring
  have hl1 : MN (l1vZ T p R γ r) := (mn_lin2 (mn_lin2 (hc 0) hy 1 (R.Au * Gw p R - γ))
    (mn_lin2 hD hM ((1 - R.Φ) * R.Au) ((1 - p.α * p.β) * (1 + p.ω)))
    (1 / ((1 - p.α * p.β) * (p.σ + p.ω))) (1 / ((1 - p.α * p.β) * (p.σ + p.ω)))).congr
      fun x => by simp only [l1vZ]; ring
  have hl4 : MN (l4vZ T p R γ r) := by
    have hin := mn_lin2 (mn_lin2 hy hπM ((1 - R.Φ) * R.Au)
      (p.α * p.β * ramseyLam p R 3 * aE p)) (hc 4) 1 1
    have hb := lb2 (lb2 (by' T r A hA hrb) (lbM T (bπ T r A hA hrb))
      ((1 - R.Φ) * R.Au) (p.α * p.β * ramseyLam p R 3 * aE p)) (g := fun y => r y 4) (cg := 1)
      (fun y => by simpa using hrb y 4) 1 1
    exact (mn_fwdS ν (abs_ab hp) hin hb).congr fun x => by simp only [l4vZ]; congr 1; funext y; ring
  have hl1l := mn_lag ν hl1
  have hl3 : MN (l3vZ T p R γ r) := by
    have e1 := mn_lin2 (hc 2) (mn_lin2 hl1 hF 1 (ramseyLam p R 0)) 1 (-1)
    have e2 := mn_lin2 hl1l (mn_lin2 hπ hF (p.θ - 1) 1) 1 (ramseyLam p R 0)
    have e3 := mn_lin2 hl4 hx 1 (-(ramseyLam p R 3 * aE p))
    have e123 := mn_lin2 (mn_lin2 e1 e2 1 p.α) e3 1 ((1 - p.α) * (aE p / p.c0))
    exact (mn_lin2 e123 hx (1 / ((1 - p.α) * ((p.θ - 1) / p.c0)))
      (ramseyLam p R 2 * (p.θ - 1))).congr fun x => by simp only [l3vZ]; ring
  refine measV_of fun i => ?_
  fin_cases i
  · exact hy.congr fun x => by simp [LinvRZ]
  · exact hπ.congr fun x => by simp [LinvRZ]
  · exact hF.congr fun x => by simp [LinvRZ]
  · exact (mn_lin2 hF hx 1 p.c0).congr fun x => by simp [LinvRZ]
  · exact hD.congr fun x => by simp [LinvRZ]
  · exact hl1.congr fun x => by simp [LinvRZ]
  · exact (mn_lin2 hM hl1 1 (-1)).congr fun x => by simp [LinvRZ]; ring
  · exact hl3.congr fun x => by simp [LinvRZ]
  · exact hl4.congr fun x => by simp [LinvRZ]


/-- Woodford (2003), Ch. 7 and App. A.3 (**the measurable Ramsey solution with purchases on the
AR(1) tree, `H = 0`**): uniform radii such that on every AR(1) tree with roots `‖d‖ ≤ δ_r ≤ δ` and
`B̄‖c‖ ≤ δ` the unique solution within `r` exists, satisfies the smallness bound, and is
measurable in `(root, innovations)` at every date. -/
theorem tree_solZ {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH0 : Hy p R sC = 0) (hAG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∃ C > 0, ∀ (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx)
      (δr : ℝ) (c : Fin 6 → ℝ), δr ≤ δ → Bx * ‖c‖ ≤ δ →
        ∃ W : Node δr Bx → Fin 9 → ℝ,
          ((∀ y, ‖W y‖ ≤ r) ∧
            PhiG (arTree ν δr Bx) (QdG p R sC) (Nd p R) (eNG ρ Bx hB c) dN W = 0) ∧
          (∀ z' : Node δr Bx → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
            PhiG (arTree ν δr Bx) (QdG p R sC) (Nd p R) (eNG ρ Bx hB c) dN z' = 0 → z' = W) ∧
          (∀ τ', 0 ≤ τ' → (∀ y, ‖PhiG (arTree ν δr Bx) (QdG p R sC) (Nd p R) (eNG ρ Bx hB c) dN
            (fun _ => 0) y‖ ≤ τ') → ∀ y, ‖W y‖ ≤ C * τ') ∧ MeasV W := by
  have hQ : ContDiff ℝ 1 (QdG p R sC) := contDiff_QdG p R sC
  obtain ⟨r, hr, δ, hδ, C, hC, hex⟩ := newton_tree.{0} hQ (contDiff_Nd p R)
    (QdG_Nd_zero R hp hs) (TidyR6bGovRamseyZero.invBound_zero R hp hs hH0 hAG)
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 6 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ))
    (r + δ)).exists_bound_of_continuousOn hQ.continuous.continuousOn
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 9 → ℝ) r).exists_bound_of_continuousOn
    ((contDiff_Nd (n := 0) p R).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self (by positivity)))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr.le))
  refine ⟨r, hr, δ, hδ, C, hC, fun ν ρ Bx hB δr c hδr hc => ?_⟩
  set T := arTree ν δr Bx
  have he : ∀ y : Node δr Bx, ‖eNG ρ Bx hB c y‖ ≤ δ := fun y => by
    simp only [eNG, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (stateN ρ Bx hB y).2 (norm_nonneg c)).trans hc
  have hd : ∀ y : Node δr Bx, ‖dN y‖ ≤ δ := fun y => y.1.1.2.trans hδr
  obtain ⟨W, hWE, hWu, hWs, hWinv⟩ := hex T _ _ he hd
  refine ⟨W, hWE, hWu, hWs, hWinv MeasV (fun n => measurable_const) (fun w hw hwm => ?_)
    (fun ws w hws _ hlim n => measurable_of_tendsto_metrizable (fun m => hws m n)
      (tendsto_pi_nhds.2 fun v => hlim _))⟩
  -- the Newton step preserves measurability
  have hlagB : ∀ y, ‖lagI T w dN y‖ ≤ r + δ := fun y => by
    unfold lagI; split_ifs
    · exact (hd y).trans (by linarith)
    · exact (hw _).trans (by linarith)
  have hNB : ∀ y, ‖Nd p R (w y)‖ ≤ CN := fun y =>
    hCN _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw y)
  have hPB : ∀ y, ‖PhiG T (QdG p R sC) (Nd p R) (eNG ρ Bx hB c) dN w y‖ ≤ CQ + CN := fun y => by
    refine (norm_add_le _ _).trans (add_le_add (hCQ _ ?_) (Mv_norm_le T.markov hCN0 hNB y))
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le ((he y).trans (by linarith)) (max_le (hlagB y) ((hw y).trans (by linarith)))
  have hPm : MeasV (PhiG T (QdG p R sC) (Nd p R) (eNG ρ Bx hB c) dN w) := by
    intro n
    have h1 : Measurable (fun v : Root δr Bx × (Fin n → ℝ) =>
        QdG p R sC (eNG ρ Bx hB c (v.1, List.ofFn v.2), lagI T w dN (v.1, List.ofFn v.2),
          w (v.1, List.ofFn v.2))) :=
      hQ.continuous.measurable.comp ((measV_eNG ρ hB c n).prodMk
        ((measV_lagI ν hwm n).prodMk (hwm n)))
    have h2 := measV_Mv ν (h := fun y => Nd p R (w y))
      (fun n => (contDiff_Nd (n := 0) p R).continuous.measurable.comp (hwm n)) hNB n
    exact h1.add h2
  have hL := measV_LinvRZ ν R hp hH0 hAG hPm (A := CQ + CN) (by positivity) fun y k => by
    have := (norm_le_pi_norm _ k).trans (hPB y); rwa [Real.norm_eq_abs] at this
  exact fun n => (hwm n).sub (hL n)


/-! ## The Markov representation on the i.i.d. probability space -/

open ExpectationsMeasure ExpectationsMeasureIID NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted
open NonlinearNKMarkovRamseyAEIFT TidyR6bGovRamseyAE

/-- Woodford (2003), Ch. 6, §5, Ch. 7, §1–2, Ch. 6, §1 and App. A.3 (**THE MARKOV REPRESENTATION
OF THE A.S. RAMSEY EQUILIBRIUM WITH GOVERNMENT PURCHASES AND AN AR(1) OF ANY BOUNDED LAW**): if
`s_C > 0`, `H = 0` and `A_uG ≠ 0`, there are
`r, δ > 0` such that for every innovation law `ν` with `|ε| ≤ B` a.s., every `|ρ| < 1`, every
`c` with `B‖c‖/(1−|ρ|) ≤ δ` and every predetermined initial value `‖d₀‖ ≤ δ`, on the i.i.d.
product space with `x_t = ρx_{t−1} + ε_t` and `e_t = x_t c` there is ONE measurable
`G : ℝ⁹ × ℝ → ℝ⁹`, independent of the date and depending on the lag only through
`(Δ̂, λ̂₁, λ̂₂)`, and an adapted solution `z` of the TRUE Ramsey
conditions with consumption `Y − G` with `‖z_t‖ ≤ r` a.s. such that `z_t = G(z_{t−1}, x_t)`
a.s. (`z_{−1} = d₀`), and every adapted solution within `r` is a.s. equal to `z`. -/
theorem gov_ramsey_ar1_markov_zero {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH0 : Hy p R sC = 0) (hAG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∀ (ν : ProbabilityMeasure ℝ) (B ρ : ℝ), |ρ| < 1 →
      (∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) → ∀ c : Fin 6 → ℝ, B / (1 - |ρ|) * ‖c‖ ≤ δ →
        ∀ d0 : Fin 9 → ℝ, ‖d0‖ ≤ δ →
          ∃ G : (Fin 9 → ℝ) → ℝ → Fin 9 → ℝ, Measurable (fun q : (Fin 9 → ℝ) × ℝ => G q.1 q.2) ∧
          (∀ d d' : Fin 9 → ℝ, ‖d‖ ≤ δ → ‖d'‖ ≤ δ → d 4 = d' 4 → d 5 = d' 5 → d 6 = d' 6 →
            ∀ x, G d x = G d' x) ∧
          ∃ z : ℕ → (ℕ → ℝ) → Fin 9 → ℝ,
            (AdA (iidSystem ν) z ∧ Bd (iidSystem ν) z r ∧ ∀ t,
              PhiTrueA (iidSystem ν) p R sC (fun t ω => ar1 ρ t ω • c) (fun _ => d0) z t
                =ᵐ[(iidSystem ν).μ] 0) ∧
            (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ,
              z t ω = G (lagIA z (fun _ => d0) t ω) (ar1 ρ t ω)) ∧
            ∀ z' : ℕ → (ℕ → ℝ) → Fin 9 → ℝ, AdA (iidSystem ν) z' → Bd (iidSystem ν) z' r →
              (∀ t, PhiTrueA (iidSystem ν) p R sC (fun t ω => ar1 ρ t ω • c) (fun _ => d0) z' t
                =ᵐ[(iidSystem ν).μ] 0) → ∀ t, z' t =ᵐ[(iidSystem ν).μ] z t := by
  classical
  obtain ⟨rt, hrt, δt, hδt, Ct, hCt, htree⟩ := tree_solZ R hp hs hH0 hAG
  obtain ⟨ra, hra, δa, hδa, hae⟩ :=
    TidyR6bGovRamseyAEZero.gov_ramsey_existence_ae_zero.{0} R hp hs hH0 hAG
  set s0 := min δt (min ra (sC / 4)) with hs0
  have hs00 : 0 < s0 := lt_min hδt (lt_min hra (by positivity))
  set τ' := s0 / Ct with hτ'
  have hτ'0 : 0 < τ' := by positivity
  obtain ⟨ρc, hρc, hQc⟩ := Metric.continuousAt_iff.1
    ((contDiff_QdG (n := 0) p R sC).continuous.continuousAt (x := 0)) τ' hτ'0
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 9 → ℝ) rt).exists_bound_of_continuousOn
    ((contDiff_Nd (n := 0) p R).continuous.continuousOn)
  set δ := min (min δt (ρc / 2)) (min δa (sC / 4)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hδt (by positivity)) (lt_min hδa (by positivity))
  have hδt' : δ ≤ δt := (min_le_left _ _).trans (min_le_left _ _)
  have hδc : δ ≤ ρc / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδa' : δ ≤ δa := (min_le_right _ _).trans (min_le_left _ _)
  have hδs : δ ≤ sC / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ra, hra, δ, hδ0, fun ν B ρ hρ hB c hc d0 hd0 => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hB.exists
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hx₀
  have h1ρ : 0 < 1 - |ρ| := by linarith
  set Bx := B / (1 - |ρ|) with hBx
  have hBx0 : 0 ≤ Bx := div_nonneg hB0 h1ρ.le
  -- the two trees
  obtain ⟨W1, ⟨hW1B, hW1E⟩, hW1u, -, hW1m⟩ := htree ν ρ Bx hBx0 δt c le_rfl (hc.trans hδt')
  obtain ⟨W2, ⟨hW2B, hW2E⟩, -, hW2s, hW2m⟩ := htree ν ρ Bx hBx0 δ c hδt' (hc.trans hδt')
  have hW2small : ∀ y, ‖W2 y‖ ≤ s0 := by
    have hb : ∀ y, ‖PhiG (arTree ν δ Bx) (QdG p R sC) (Nd p R) (eNG ρ Bx hBx0 c) dN
        (fun _ => 0) y‖ ≤ τ' := by
      intro y
      have hss := QdG_Nd_zero R hp hs
      have e1 : PhiG (arTree ν δ Bx) (QdG p R sC) (Nd p R) (eNG ρ Bx hBx0 c) dN (fun _ => 0) y =
          QdG p R sC (eNG ρ Bx hBx0 c y, lagI (arTree ν δ Bx) (fun _ => 0) dN y, 0) -
            QdG p R sC 0 := by
        simp only [PhiG, Mv_const (arTree ν δ Bx).markov]
        rw [eq_neg_of_add_eq_zero_right hss]
        abel
      rw [e1, ← dist_eq_norm]
      refine (hQc ?_).le
      rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
      have he : ‖eNG ρ Bx hBx0 c y‖ ≤ ρc / 2 := by
        simp only [eNG, norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (stateN ρ Bx hBx0 y).2 (norm_nonneg c)).trans
          (hc.trans hδc)
      have hl : ‖lagI (arTree ν δ Bx) (fun _ => (0 : Fin 9 → ℝ)) dN y‖ ≤ ρc / 2 := by
        unfold lagI; split_ifs
        · exact y.1.1.2.trans hδc
        · rw [norm_zero]; positivity
      have h0 : ‖(0 : Fin 9 → ℝ)‖ ≤ ρc / 2 := by rw [norm_zero]; positivity
      exact lt_of_le_of_lt (max_le he (max_le hl h0)) (by linarith)
    intro y
    exact (hW2s τ' hτ'0.le hb y).trans (le_of_eq (by rw [hτ']; field_simp))
  -- the policy function
  obtain ⟨cb, hcb⟩ : ∃ cb : (Fin 9 → ℝ) → Fin 9 → ℝ,
      cb = fun d => if ‖d‖ ≤ δt then d else 0 := ⟨_, rfl⟩
  have hcbB : ∀ d, ‖cb d‖ ≤ δt := fun d => by
    rw [hcb]; dsimp only; split_ifs with h
    · exact h
    · rw [norm_zero]; exact hδt.le
  have hcbm : Measurable cb := by
    rw [hcb]
    exact Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
      measurable_id measurable_const
  obtain ⟨rt1, hrt1⟩ : ∃ rt1 : (Fin 9 → ℝ) × ℝ → Root δt Bx,
      rt1 = fun q => (⟨cb q.1, hcbB q.1⟩, clampX Bx hBx0 q.2) := ⟨_, rfl⟩
  have hrt1m : Measurable rt1 := by
    rw [hrt1]
    exact ((hcbm.comp measurable_fst).subtype_mk).prodMk
      ((continuous_clampX Bx hBx0).measurable.comp measurable_snd)
  obtain ⟨G, hGdef⟩ : ∃ G : (Fin 9 → ℝ) → ℝ → Fin 9 → ℝ,
      G = fun d x => W1 (rt1 (d, x), []) := ⟨_, rfl⟩
  have hGm : Measurable (fun q : (Fin 9 → ℝ) × ℝ => G q.1 q.2) := by
    have h0 := (hW1m 0).comp (hrt1m.prodMk (measurable_const (a := (Fin.elim0 : Fin 0 → ℝ))))
    have e : (fun q : (Fin 9 → ℝ) × ℝ => G q.1 q.2) = fun q =>
        W1 ((rt1 q, (Fin.elim0 : Fin 0 → ℝ)).1, List.ofFn (rt1 q, (Fin.elim0 : Fin 0 → ℝ)).2) := by
      funext q; rw [hGdef]; rfl
    rw [e]; exact h0
  -- the process along the tree of `W₂`
  set E := iidSystem ν with hE
  set root2 : (ℕ → ℝ) → Root δ Bx := fun ω => (⟨d0, hd0⟩, clampX Bx hBx0 (ω 0)) with hroot2
  set node : ℕ → (ℕ → ℝ) → Node δ Bx := fun t ω => (root2 ω, List.ofFn (innov t ω)) with hnode
  set z : ℕ → (ℕ → ℝ) → Fin 9 → ℝ := fun t ω => W2 (node t ω) with hz
  have hroot2m : ∀ t, Measurable[E.𝓕 t] root2 := fun t => by
    let _ := E.𝓕 t
    exact measurable_const.prodMk ((continuous_clampX Bx hBx0).measurable.comp
      (measurable_shock ν (Nat.zero_le t)))
  have hWv : ∀ t, Measurable[E.𝓕 t] (fun ω => (root2 ω, innov t ω)) := fun t => by
    let _ := E.𝓕 t
    exact (hroot2m t).prodMk (measurable_innov ν t)
  have hzm : ∀ t, Measurable[E.𝓕 t] (z t) := fun t => (hW2m t).comp (hWv t)
  have hzA : AdA E z := fun t => by
    let _ := E.𝓕 t
    exact (hzm t).aestronglyMeasurable
  have hzB : Bd E z ra := fun t => Eventually.of_forall fun ω =>
    (hW2small _).trans ((min_le_right _ _).trans (min_le_left _ _))
  -- the state along the path
  have har : ∀ t, ∀ᵐ ω ∂E.μ, |ar1 ρ t ω| ≤ Bx := fun t => ar1_bdd (ν := ν) hρ hB t
  have hstate : ∀ t, ∀ᵐ ω ∂E.μ, (stateN ρ Bx hBx0 (node t ω) : ℝ) = ar1 ρ t ω := fun t => by
    filter_upwards [ae_all_iff.2 har] with ω h
    induction t with
    | zero =>
      have h0 : |ω 0| ≤ Bx := h 0
      simp only [hnode, hroot2, stateN, List.ofFn_zero, List.foldl_nil]
      exact clampX_of hBx0 h0
    | succ t ih =>
      have e : node (t + 1) ω = ((node t ω).1, (node t ω).2 ++ [ω (t + 1)]) := by
        simp only [hnode, ofFn_innov_succ]
      rw [e, stateN_snoc]
      simp only [arSucc, ih]
      have h1 : |ρ * ar1 ρ t ω + ω (t + 1)| ≤ Bx := h (t + 1)
      rw [clampX_of hBx0 h1]
      rfl
  -- the lag of the process is the tree lag
  have hlag : ∀ t ω, lagI (arTree ν δ Bx) W2 dN (node t ω) = lagIA z (fun _ => d0) t ω := by
    intro t ω
    cases t with
    | zero => simp [lagI, arTree, hnode, dN, lagIA, hroot2]
    | succ t =>
      have e : node (t + 1) ω = ((node t ω).1, (node t ω).2 ++ [ω (t + 1)]) := by
        simp only [hnode, ofFn_innov_succ]
      rw [e]
      simp [lagI, arTree, lagIA, hz]
  -- the forecasts are the tree expectations
  have hNB : ∀ y, ‖Nd p R (W2 y)‖ ≤ CN := fun y =>
    hCN _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hW2B y)
  have hfc : ∀ t (i : Fin 9), E.E t (fun ω' => Nd p R (z (t + 1) ω') i) =ᵐ[E.μ]
      fun ω => ΛR ν (fun ε => Nd p R (W2 ((node t ω).1, (node t ω).2 ++ [ε])) i) := by
    intro t i
    set F : (Root δ Bx × (Fin t → ℝ)) × ℝ → ℝ := fun q =>
      Nd p R (W2 (q.1.1, List.ofFn (Fin.snoc q.1.2 q.2 : Fin (t + 1) → ℝ))) i with hF
    have hFm : Measurable F := (measurable_pi_apply i).comp
      ((contDiff_Nd (n := 0) p R).continuous.measurable.comp ((hW2m (t + 1)).comp
        ((measurable_fst.comp measurable_fst).prodMk ((measurable_snoc' t).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))))
    have hFb : ∀ q, |F q| ≤ CN := fun q => by
      have := (norm_le_pi_norm _ i).trans (hNB (q.1.1, List.ofFn (Fin.snoc q.1.2 q.2 :
        Fin (t + 1) → ℝ)))
      rwa [Real.norm_eq_abs] at this
    have hY : Measurable fun ω : ℕ → ℝ => ω (t + 1) := measurable_pi_apply (t + 1)
    have hind : Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ => ω (t + 1)) inferInstance)
        (E.𝓕 t) E.μ :=
      indep_of_indep_of_le_left (indep_future ν t)
        (measurable_future_fun t measurable_id).comap_le
    have hfr := freeze (μ := E.μ) (E.𝓕.le t) (hWv t) hY hind hFm hFb
    have hlaw : E.μ.map (fun ω : ℕ → ℝ => ω (t + 1)) = (ν : Measure ℝ) :=
      Measure.infinitePi_map_eval _ (t + 1)
    have e1 : (fun ω' => Nd p R (z (t + 1) ω') i) =
        fun ω' => F ((root2 ω', innov t ω'), ω' (t + 1)) := by
      funext ω'
      simp only [hF, hz, hnode, ofFn_snoc, ofFn_innov_succ]
    rw [e1]
    filter_upwards [hfr] with ω h
    refine h.trans ?_
    rw [hlaw]
    have hm : Measurable (fun ε => Nd p R (W2 ((node t ω).1, (node t ω).2 ++ [ε])) i) :=
      (measurable_pi_apply i).comp ((contDiff_Nd (n := 0) p R).continuous.measurable.comp
        (hW2m.slice (node t ω)))
    rw [(ΛR_spec ν).1 _ hm ⟨CN, fun ε => by
      have := (norm_le_pi_norm _ i).trans (hNB ((node t ω).1, (node t ω).2 ++ [ε]))
      rwa [Real.norm_eq_abs] at this⟩]
    simp only [hF, ofFn_snoc, hnode]
  -- the process solves the Ramsey conditions a.s.
  have hzE0 : ∀ t, TidyR6bRamseyNewtonAE.PhiGA E (QdG p R sC) (Nd p R)
      (fun t ω => ar1 ρ t ω • c) (fun _ => d0) z t =ᵐ[E.μ] 0 := by
    intro t
    filter_upwards [hstate t, ae_all_iff.2 (hfc t)] with ω hs hf
    have hT := congrFun hW2E (node t ω)
    rw [PhiG_ar] at hT
    simp only [Pi.zero_apply] at hT ⊢
    have hl := hlag t ω
    simp only [lagI, arTree] at hl
    have hm : MvA E (fun s ω' => Nd p R (z s ω')) t ω =
        fun i => ΛR ν (fun ε => Nd p R (W2 ((node t ω).1, (node t ω).2 ++ [ε])) i) :=
      funext fun i => hf i
    have he : ar1 ρ t ω • c = eNG ρ Bx hBx0 c (node t ω) := by simp only [eNG, hs]
    simp only [TidyR6bRamseyNewtonAE.PhiGA, hm, he]
    rw [← hl]
    exact hT
  -- the Markov representation
  have hzG : ∀ t, ∀ᵐ ω ∂E.μ, z t ω = G (lagIA z (fun _ => d0) t ω) (ar1 ρ t ω) := by
    intro t
    filter_upwards [hstate t] with ω hs
    have hlB : ‖lagI (arTree ν δ Bx) W2 dN (node t ω)‖ ≤ δt := by
      unfold lagI; split_ifs
      · exact (node t ω).1.1.2.trans hδt'
      · exact (hW2small _).trans (min_le_left _ _)
    have hsh := shift_eqG ν ρ hBx0 (QdG p R sC) (Nd p R) c rt W1 hW1B hW1u W2 hW2B hW2E hW1E
      (node t ω) hlB
    have hroot : ((⟨lagI (arTree ν δ Bx) W2 dN (node t ω), hlB⟩,
        stateN ρ Bx hBx0 (node t ω)) : Root δt Bx) =
          rt1 (lagIA z (fun _ => d0) t ω, ar1 ρ t ω) := by
      rw [hrt1]
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change lagI (arTree ν δ Bx) W2 dN (node t ω) = cb (lagIA z (fun _ => d0) t ω)
        rw [← hlag t ω, hcb]
        simp only [hlB, ↓reduceIte]
      · change (stateN ρ Bx hBx0 (node t ω) : ℝ) = (clampX Bx hBx0 (ar1 ρ t ω) : ℝ)
        rw [← hs, clampX_of hBx0 (stateN ρ Bx hBx0 (node t ω)).2]
    rw [hz]
    simp only
    rw [hsh, hGdef]
    simp only
    rw [hroot]
  -- the smooth conditions are the true ones along the path
  have heS : Bd E (fun t ω => ar1 ρ t ω • c) (sC / 4) := fun t => by
    filter_upwards [har t] with ω hω
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hω (norm_nonneg c)).trans (hc.trans hδs)
  have hzS : Bd E z (sC / 4) := fun t => Eventually.of_forall fun ω =>
    (hW2small _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzE : ∀ t, PhiTrueA E p R sC (fun t ω => ar1 ρ t ω • c) (fun _ => d0) z t =ᵐ[E.μ] 0 :=
    fun t => by
      filter_upwards [PhiTrueA_ae E R hs heS hzS t, hzE0 t] with ω h1 h2
      rw [h1, h2]
  -- uniqueness among adapted solutions
  have heA : AdA E (fun t ω => ar1 ρ t ω • c) := fun t => by
    let _ := E.𝓕 t
    exact ((ar1_adapted ν ρ t).measurable.smul_const c).aestronglyMeasurable
  have heB : Bd E (fun t ω => ar1 ρ t ω • c) δa := fun t => by
    filter_upwards [har t] with ω hω
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hω (norm_nonneg c)).trans (hc.trans hδa')
  obtain ⟨zA, -, huA⟩ := hae (ℕ → ℝ) E (fun t ω => ar1 ρ t ω • c) (fun _ => d0) heA heB
    aestronglyMeasurable_const (Eventually.of_forall fun _ => hd0.trans hδa')
  have hGc : ∀ d d' : Fin 9 → ℝ, ‖d‖ ≤ δ → ‖d'‖ ≤ δ → d 4 = d' 4 → d 5 = d' 5 →
      d 6 = d' 6 → ∀ x, G d x = G d' x := by
    intro d d' hd hd' h4 h5 h6 x
    have hcd : cb d = d := by rw [hcb]; simp only [hd.trans hδt', ↓reduceIte]
    have hcd' : cb d' = d' := by rw [hcb]; simp only [hd'.trans hδt', ↓reduceIte]
    rw [hGdef]
    simp only
    refine (tree_root_congrG ν ρ hBx0 R sC c rt W1 hW1B hW1u hW1E (rt1 (d', x)) (rt1 (d, x))
      (by rw [hrt1]) ?_ ?_ ?_)
    · rw [hrt1]; simp only [hcd, hcd', h4]
    · rw [hrt1]; simp only [hcd, hcd', h5]
    · rw [hrt1]; simp only [hcd, hcd', h6]
  refine ⟨G, hGm, hGc, z, ⟨hzA, hzB, hzE⟩, hzG, fun z' hz'A hz'B hz' t => ?_⟩
  filter_upwards [huA z' hz'A hz'B hz' t, huA z hzA hzB hzE t] with ω h1 h2
  rw [h1, h2]

end Woodford.StabilizationWelfare.TidyR6bGovRamseyAR1Zero
