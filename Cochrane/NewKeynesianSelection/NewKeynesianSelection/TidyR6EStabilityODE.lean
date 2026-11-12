/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6EStability
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Instability of the E-stability dynamics for the T-maps of §16.10.7

Cochrane (2023), §16.10.7, p. 394, with E-stability defined as in Woodford (2003), Ch. 4, p. 266
(module TidyR6EStability): a rest point of `θ̇ = T(θ) − θ` is E-stable when the eigenvalues of
`DT − I` have negative real parts. This module proves that, for the T-maps of the chapter, failure
of E-stability is genuine instability of the learning dynamics (not only of their
linearisation).

## Main results

* The scalar steady-state T-map of Figure 16.2 (any `T` with `T(x̄) = x̄`, `T′(x̄) = a > 1`):
  `unstable_exits` (every solution starting near but off `x̄` leaves a fixed neighbourhood),
  `not_lyapunov_stable` (with solutions from every initial point, `x̄` is not Lyapunov stable).
  For a rule with slope `d ∈ (0, 1)` at `Π_L` that is affine near `Π_L`, the T-map is affine and
  solutions exist: `affine_tmap_esol_exists`, `lower_not_lyapunov_stable_affine`.
* The two-dimensional MSV T-map of (16.1)–(16.2) (`TidyR6EStability.tMap`): `IsESol2`,
  `esol2_components` (the components solve scalar linear equations), `msv_esol2_eq` (closed
  form), `msv_esol2_exists`, `msv_tendsto_iff_eStable` (every solution converges iff the MSV
  equilibrium is E-stable), `msv_unstable_of_not_eStable` (otherwise there are solutions
  starting arbitrarily close that do not converge) and `msv_lyapunov_iff_eStable`.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6EStabilityODE

open Filter Topology TidyR6EStability

/-! ## The scalar T-map -/

/-- Cochrane (2023), §16.10.7, p. 394: if `T(x̄) = x̄` and `T′(x̄) = a > 1` there is `ε > 0` such
that every solution of `θ̇ = T(θ) − θ` with `0 < |θ(0) − x̄| < ε` leaves the `ε`-neighbourhood
at some time `τ ≥ 0`. -/
theorem unstable_exits {T : ℝ → ℝ} {xb a : ℝ} (hfix : T xb = xb) (hT : HasDerivAt T a xb)
    (ha : 1 < a) :
    ∃ ε > 0, ∀ θ, IsESol1 T θ → 0 < |θ 0 - xb| → |θ 0 - xb| < ε →
      ∃ τ, 0 ≤ τ ∧ ε ≤ |θ τ - xb| := by
  set c : ℝ := (a - 1) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨δ, hδ, hb⟩ := field_bounds hfix hT hc0
  refine ⟨δ, hδ, fun θ hθ h0 _ => ?_⟩
  by_contra hcon
  push Not at hcon
  set V : ℝ → ℝ := fun τ => (θ τ - xb) ^ 2 with hV
  set W : ℝ → ℝ := fun τ => Real.exp (-(2 * c * τ)) * V τ with hW
  have hWd : ∀ τ, HasDerivAt W (Real.exp (-(2 * c * τ)) *
      (-(2 * c * V τ) + 2 * ((T (θ τ) - θ τ) * (θ τ - xb)))) τ := by
    intro τ
    have hl : HasDerivAt (fun τ : ℝ => -(2 * c * τ)) (-(2 * c)) τ := by
      convert ((hasDerivAt_id' τ).const_mul (2 * c)).neg using 1; ring
    have h1 : HasDerivAt (fun τ => Real.exp (-(2 * c * τ)))
        (Real.exp (-(2 * c * τ)) * (-(2 * c))) τ := hl.exp
    have h2 : HasDerivAt V (2 * (θ τ - xb) * (T (θ τ) - θ τ)) τ := by
      have := ((hθ τ).sub_const xb).pow 2
      convert this using 1; simp
    convert h1.mul h2 using 1; ring
  have hWc : Continuous W := continuous_iff_continuousAt.mpr fun τ => (hWd τ).continuousAt
  have hmono : MonotoneOn W (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hWc.continuousOn
    · intro τ _
      exact (hWd τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Ici] at hτ
      rw [(hWd τ).deriv]
      have := (hb (θ τ) (hcon τ (le_of_lt hτ))).2
      have : 0 ≤ -(2 * c * V τ) + 2 * ((T (θ τ) - θ τ) * (θ τ - xb)) := by
        simp only [hV]; nlinarith
      exact mul_nonneg (Real.exp_pos _).le this
  have hV0 : 0 < V 0 := by
    simp only [hV]; nlinarith [sq_abs (θ 0 - xb), mul_pos h0 h0]
  -- `V τ ≥ e^{2cτ} V 0`, unbounded, against `V τ < δ²`
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, δ ^ 2 / V 0 < Real.exp (2 * c * τ) ∧ 0 ≤ τ := by
    obtain ⟨n, hn⟩ := exists_nat_gt (δ ^ 2 / V 0)
    refine ⟨n / (2 * c), ?_, by positivity⟩
    have : (n : ℝ) < Real.exp (n : ℝ) := by
      have := Real.add_one_le_exp (n : ℝ); linarith
    calc δ ^ 2 / V 0 < n := hn
      _ < Real.exp n := this
      _ = Real.exp (2 * c * (n / (2 * c))) := by congr 1; field_simp
  have hWm := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hτ.2) hτ.2
  simp only [hW, mul_zero, neg_zero, Real.exp_zero, one_mul] at hWm
  have hbig : δ ^ 2 < Real.exp (2 * c * τ) * V 0 := by
    have := hτ.1; rw [div_lt_iff₀ hV0] at this; linarith
  have hVτ : V τ < δ ^ 2 := by
    simp only [hV]
    have := hcon τ hτ.2
    nlinarith [abs_nonneg (θ τ - xb), sq_abs (θ τ - xb)]
  have he : Real.exp (2 * c * τ) * Real.exp (-(2 * c * τ)) = 1 := by
    rw [← Real.exp_add]; simp
  have : Real.exp (2 * c * τ) * V 0 ≤ V τ := by
    calc Real.exp (2 * c * τ) * V 0 ≤ Real.exp (2 * c * τ) * (Real.exp (-(2 * c * τ)) * V τ) :=
          mul_le_mul_of_nonneg_left hWm (Real.exp_pos _).le
      _ = V τ := by rw [← mul_assoc, he, one_mul]
  linarith

/-- Cochrane (2023), §16.10.7, p. 394, Lyapunov instability: if `T(x̄) = x̄`, `T′(x̄) > 1` and
the learning dynamics have a solution from every initial belief, `x̄` is not Lyapunov stable:
for some `ε > 0`, every neighbourhood of `x̄` contains initial beliefs whose path leaves the
`ε`-neighbourhood. -/
theorem not_lyapunov_stable {T : ℝ → ℝ} {xb a : ℝ} (hfix : T xb = xb) (hT : HasDerivAt T a xb)
    (ha : 1 < a) (hex : ∀ x0, ∃ θ, IsESol1 T θ ∧ θ 0 = x0) :
    ¬ ∀ ε > 0, ∃ δ > 0, ∀ θ, IsESol1 T θ → |θ 0 - xb| < δ → ∀ τ, 0 ≤ τ → |θ τ - xb| < ε := by
  intro hstab
  obtain ⟨ε, hε, hexit⟩ := unstable_exits hfix hT ha
  obtain ⟨δ, hδ, hδε⟩ := hstab ε hε
  set x0 := xb + min (δ / 2) (ε / 2) with hx0
  have hm : 0 < min (δ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
  obtain ⟨θ, hθ, h0⟩ := hex x0
  have hd : |θ 0 - xb| = min (δ / 2) (ε / 2) := by rw [h0, hx0]; simp [abs_of_pos hm]
  obtain ⟨τ, hτ, hτε⟩ := hexit θ hθ (by rw [hd]; exact hm)
    (by rw [hd]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have := hδε θ hθ (by rw [hd]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)) τ hτ
  linarith

/-- Cochrane (2023), §16.10.7, p. 394: an affine T-map `T(x) = x̄ + a(x − x̄)` has a solution of the
learning dynamics from every initial belief. -/
theorem affine_tmap_esol_exists (a xb x0 : ℝ) :
    ∃ θ, IsESol1 (fun x => xb + a * (x - xb)) θ ∧ θ 0 = x0 :=
  ⟨_, esol_linear_sol a xb x0, by simp⟩

/-- Cochrane (2023), p. 379 and §16.10.7, p. 394: if near `Π_L` the rule is affine with slope
`d ∈ (0, 1)`, `Φ(Π) = Π_L + d(Π − Π_L)`, its steady-state T-map `T(Πᵉ) = Π_L + (Πᵉ − Π_L)/d`
(`Φ(T(Πᵉ)) = Πᵉ`) has slope `1/d > 1`, and `Π_L` is not Lyapunov stable under learning: the
passive steady state is unstable, not merely non-E-stable. -/
theorem lower_not_lyapunov_stable_affine {PL d : ℝ} (hd0 : 0 < d) (hd1 : d < 1) :
    (∀ p, PL + d * ((PL + d⁻¹ * (p - PL)) - PL) = p) ∧
    ¬ ∀ ε > 0, ∃ δ > 0, ∀ θ, IsESol1 (fun x => PL + d⁻¹ * (x - PL)) θ → |θ 0 - PL| < δ →
      ∀ τ, 0 ≤ τ → |θ τ - PL| < ε := by
  refine ⟨fun p => by field_simp; ring, ?_⟩
  have hT : HasDerivAt (fun x => PL + d⁻¹ * (x - PL)) d⁻¹ PL := by
    convert (((hasDerivAt_id' PL).sub_const PL).const_mul d⁻¹).const_add PL using 1; ring
  exact not_lyapunov_stable (by simp) hT ((one_lt_inv₀ hd0).mpr hd1)
    (affine_tmap_esol_exists _ _)

/-! ## The MSV T-map of (16.1)–(16.2) -/

/-- Cochrane (2023), §16.10.7, p. 394, and Woodford (2003), (2.20), p. 265: `θ : ℝ → ℝ²` solves
the E-stability equation `θ̇ = T(θ) − θ` for the MSV T-map. -/
def IsESol2 (φ η : ℝ) (θ : ℝ → Fin 2 → ℝ) : Prop :=
  ∀ τ, HasDerivAt θ (tMap φ η (θ τ) - θ τ) τ

/-- Cochrane (2023), §16.10.7, p. 394: the components of a solution solve scalar linear
equations, `θ̇₀ = (0 + φ⁻¹(θ₀ − 0)) − θ₀` and `θ̇₁ = (b̄ + (η/φ)(θ₁ − b̄)) − θ₁`,
`b̄ = −1/(φ − η)` (for `φ ≠ 0`, `φ ≠ η`). -/
theorem esol2_components {φ η : ℝ} (hφ : φ ≠ 0) (hη : φ ≠ η) {θ : ℝ → Fin 2 → ℝ}
    (h : IsESol2 φ η θ) :
    IsESol1 (fun x => 0 + φ⁻¹ * (x - 0)) (fun τ => θ τ 0) ∧
      IsESol1 (fun x => -(φ - η)⁻¹ + η / φ * (x - -(φ - η)⁻¹)) (fun τ => θ τ 1) := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hη
  refine ⟨fun τ => ?_, fun τ => ?_⟩
  · have := (hasDerivAt_pi.mp (h τ)) 0
    convert this using 1
    simp [tMap]; ring
  · have := (hasDerivAt_pi.mp (h τ)) 1
    convert this using 1
    simp only [tMap, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring

/-- Cochrane (2023), §16.10.7, p. 394: every solution of the MSV learning dynamics is
`θ(τ) = θ̄ + (e^{(φ⁻¹−1)τ}(θ₀(0) − 0), e^{(η/φ−1)τ}(θ₁(0) − b̄))`. -/
theorem msv_esol2_eq {φ η : ℝ} (hφ : φ ≠ 0) (hη : φ ≠ η) {θ : ℝ → Fin 2 → ℝ}
    (h : IsESol2 φ η θ) (τ : ℝ) :
    θ τ 0 = 0 + Real.exp ((φ⁻¹ - 1) * τ) * (θ 0 0 - 0) ∧
      θ τ 1 = -(φ - η)⁻¹ + Real.exp ((η / φ - 1) * τ) * (θ 0 1 - -(φ - η)⁻¹) := by
  obtain ⟨h0, h1⟩ := esol2_components hφ hη h
  exact ⟨esol_linear_eq h0 τ, esol_linear_eq h1 τ⟩

/-- Cochrane (2023), §16.10.7, p. 394: the closed form is a solution, from every initial
belief. -/
theorem msv_esol2_exists {φ η : ℝ} (hφ : φ ≠ 0) (hη : φ ≠ η) (x0 : Fin 2 → ℝ) :
    ∃ θ, IsESol2 φ η θ ∧ θ 0 = x0 := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hη
  set θ : ℝ → Fin 2 → ℝ := fun τ => ![0 + Real.exp ((φ⁻¹ - 1) * τ) * (x0 0 - 0),
    -(φ - η)⁻¹ + Real.exp ((η / φ - 1) * τ) * (x0 1 - -(φ - η)⁻¹)] with hθ
  refine ⟨θ, fun τ => ?_, ?_⟩
  · rw [hasDerivAt_pi]
    intro i
    have hd0 : HasDerivAt (fun τ => θ τ 0) ((tMap φ η (θ τ) - θ τ) 0) τ := by
      have := esol_linear_sol φ⁻¹ 0 (x0 0) τ
      have e : (tMap φ η (θ τ) - θ τ) 0 = (0 + φ⁻¹ * (θ τ 0 - 0)) - θ τ 0 := by
        simp only [Pi.sub_apply, tMap, Matrix.cons_val_zero]; field_simp; ring
      rw [e]; exact this
    have hd1 : HasDerivAt (fun τ => θ τ 1) ((tMap φ η (θ τ) - θ τ) 1) τ := by
      have := esol_linear_sol (η / φ) (-(φ - η)⁻¹) (x0 1) τ
      have e : (tMap φ η (θ τ) - θ τ) 1 =
          (-(φ - η)⁻¹ + η / φ * (θ τ 1 - -(φ - η)⁻¹)) - θ τ 1 := by
        simp only [Pi.sub_apply, tMap, Matrix.cons_val_one, Matrix.cons_val_fin_one]
        field_simp
        ring
      rw [e]; exact this
    fin_cases i
    · exact hd0
    · exact hd1
  · funext i
    fin_cases i <;> simp [hθ]

/-- Cochrane (2023), §16.10.7, p. 394, and Woodford (2003), p. 266: for `φ ≠ 0, 1, η`, every
solution of the MSV learning dynamics converges to the MSV equilibrium iff the MSV equilibrium
is E-stable. -/
theorem msv_tendsto_iff_eStable {φ η : ℝ} (hφ : φ ≠ 0) (h1 : φ ≠ 1) (hη : φ ≠ η) :
    (∀ θ, IsESol2 φ η θ → ∀ i, Tendsto (fun τ => θ τ i) atTop
      (𝓝 ((![0, -(φ - η)⁻¹] : Fin 2 → ℝ) i))) ↔ EStableAt (tMap φ η) ![0, -(φ - η)⁻¹] := by
  rw [msv_eStable_iff hφ h1 hη, ← esol_linear_tendsto_iff φ⁻¹ 0,
    ← esol_linear_tendsto_iff (η / φ) (-(φ - η)⁻¹)]
  constructor
  · intro h
    refine ⟨fun θ0 hθ0 => ?_, fun θ1 hθ1 => ?_⟩
    · obtain ⟨θ, hθ, hθi⟩ := msv_esol2_exists hφ hη ![θ0 0, -(φ - η)⁻¹]
      have := h θ hθ 0
      have e : (fun τ => θ τ 0) = θ0 := by
        funext τ
        rw [(msv_esol2_eq hφ hη hθ τ).1, esol_linear_eq hθ0 τ, hθi]
        simp
      simpa [e] using this
    · obtain ⟨θ, hθ, hθi⟩ := msv_esol2_exists hφ hη ![0, θ1 0]
      have := h θ hθ 1
      have e : (fun τ => θ τ 1) = θ1 := by
        funext τ
        rw [(msv_esol2_eq hφ hη hθ τ).2, esol_linear_eq hθ1 τ, hθi]
        simp
      simpa [e] using this
  · rintro ⟨h0, h1'⟩ θ hθ i
    obtain ⟨c0, c1⟩ := esol2_components hφ hη hθ
    fin_cases i
    · simpa using h0 _ c0
    · simpa using h1' _ c1

/-- Cochrane (2023), §16.10.7, p. 394: if the MSV equilibrium is not E-stable, for every
`δ > 0` some solution starting within `δ` of it (in each coordinate) does not converge to it:
the failure of E-stability is instability of the learning dynamics. -/
theorem msv_unstable_of_not_eStable {φ η : ℝ} (hφ : φ ≠ 0) (h1 : φ ≠ 1) (hη : φ ≠ η)
    (hns : ¬ EStableAt (tMap φ η) ![0, -(φ - η)⁻¹]) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ, IsESol2 φ η θ ∧ (∀ i, |θ 0 i - (![0, -(φ - η)⁻¹] : Fin 2 → ℝ) i| < δ) ∧
      ∃ i, ¬ Tendsto (fun τ => θ τ i) atTop (𝓝 ((![0, -(φ - η)⁻¹] : Fin 2 → ℝ) i)) := by
  rw [msv_eStable_iff hφ h1 hη] at hns
  have hδ2 : 0 < δ / 2 := by linarith
  have hgrow : ∀ {a : ℝ}, 1 ≤ a → ∀ τ : ℝ, 0 ≤ τ → 1 ≤ Real.exp ((a - 1) * τ) :=
    fun ha τ hτ => Real.one_le_exp (by nlinarith)
  by_cases h0 : φ⁻¹ < 1
  · have h1' : 1 ≤ η / φ := by
      by_contra hc; push Not at hc; exact hns ⟨h0, hc⟩
    obtain ⟨θ, hθ, hθi⟩ := msv_esol2_exists hφ hη ![0, -(φ - η)⁻¹ + δ / 2]
    refine ⟨θ, hθ, fun i => ?_, 1, fun hlim => ?_⟩
    · rw [hθi]; fin_cases i <;> simp [abs_of_pos hδ2] <;> linarith
    · have hge : ∀ τ : ℝ, 0 ≤ τ → -(φ - η)⁻¹ + δ / 2 ≤ θ τ 1 := fun τ hτ => by
        rw [(msv_esol2_eq hφ hη hθ τ).2, hθi]
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        have := hgrow h1' τ hτ
        nlinarith
      have := ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, hge⟩)
      simp at this
      linarith
  · push Not at h0
    obtain ⟨θ, hθ, hθi⟩ := msv_esol2_exists hφ hη ![δ / 2, -(φ - η)⁻¹]
    refine ⟨θ, hθ, fun i => ?_, 0, fun hlim => ?_⟩
    · rw [hθi]; fin_cases i <;> simp [abs_of_pos hδ2] <;> linarith
    · have hge : ∀ τ : ℝ, 0 ≤ τ → δ / 2 ≤ θ τ 0 := fun τ hτ => by
        rw [(msv_esol2_eq hφ hη hθ τ).1, hθi]
        simp only [Matrix.cons_val_zero, sub_zero, zero_add]
        have := hgrow h0 τ hτ
        nlinarith
      have := ge_of_tendsto hlim (eventually_atTop.mpr ⟨0, hge⟩)
      simp at this
      linarith

/-- Cochrane (2023), §16.10.7, p. 394, and Woodford (2003), p. 266: for the MSV T-map,
E-stability is equivalent to asymptotic stability of the learning dynamics in the strong form
"every solution converges", and its failure gives non-converging solutions from arbitrarily close
initial beliefs. -/
theorem msv_lyapunov_iff_eStable {φ η : ℝ} (hφ : φ ≠ 0) (h1 : φ ≠ 1) (hη : φ ≠ η) :
    EStableAt (tMap φ η) ![0, -(φ - η)⁻¹] ↔
      ∀ δ > 0, ∀ θ, IsESol2 φ η θ →
        (∀ i, |θ 0 i - (![0, -(φ - η)⁻¹] : Fin 2 → ℝ) i| < δ) →
        ∀ i, Tendsto (fun τ => θ τ i) atTop (𝓝 ((![0, -(φ - η)⁻¹] : Fin 2 → ℝ) i)) := by
  constructor
  · intro h δ _ θ hθ _ i
    exact (msv_tendsto_iff_eStable hφ h1 hη).mpr h θ hθ i
  · intro h
    by_contra hns
    obtain ⟨θ, hθ, hnear, i, hi⟩ := msv_unstable_of_not_eStable hφ h1 hη hns one_pos
    exact hi (h 1 one_pos θ hθ hnear i)

end Cochrane.NewKeynesianSelection.TidyR6EStabilityODE
