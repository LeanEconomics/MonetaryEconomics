/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergCentreSecond
import StabilizationWelfare.NonlinearRotembergCentreChart

/-!
# The linear Taylor rule on the boundary: a ONE-SIDED continuum of equilibria

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254, the Taylor principle
`κ(φ_π − 1) + (1 − β)φ_y > 0`) and Appendix A.3 (pp. 632–634), for the exact Rotemberg model
(`NonlinearRotemberg`) under the LINEAR rule `1 + i_t = β⁻¹Π_t^{φ_π}(Y_t/Ȳ)^{φ_y}` on the boundary
`κ(φ_π − 1) + (1 − β)φ_y = 0` with `φ_y > 0`, under perfect foresight.

The linearisation has a unit root (`NonlinearRotembergBoundary.boundary_linear_kernel`) and does
not decide (`NonlinearRotembergBoundaryPair`). The answer is decided by the TRANSCRITICAL
coefficient `q` of the centre dynamics `L_{t+1} = L_t + qL_t² + …`
(`NonlinearRotembergCentreSecond`), whose sign is the sign of
`S = σ(θm)² + 3(1 − β)θm − (1 − β)²ψ`.
Write `s = 1` if `S > 0` and `s = −1` if `S < 0`.

## Main results

* **`one_sided`** (no equilibrium on the wrong side): there is `δ > 0` such that every exact
  perfect-foresight equilibrium with `‖x_t‖ ≤ δ` at every date has `sL_t ≤ 0`, `sL_t`
  nondecreasing, `x_t → 0`, and, unless it is the steady state, `sπ_t < 0` and `sŷ_t < 0` at
  EVERY date.
* **`continuum`** (the continuum on the right side): for every `r > 0` there is `c₀ > 0` such
  that for every `c ∈ (0, c₀]` there is an exact equilibrium with `L_0 = −sc`, `‖x_t‖ ≤ r` at every
  date, `x_t → 0`, and `sπ_t < 0`, `sŷ_t < 0` at every date; distinct `c` give distinct equilibria.
  Existence is by the Ważewski nested-interval argument
  (`NonlinearRotembergCentreTools.wazewski`) in the chart of `NonlinearRotembergCentreChart`.
* **`deflationary`**, **`inflationary`**, **`not_locally_unique`**: both together.
  With `S > 0` the continuum is DEFLATIONARY
  (`π_t < 0`, `ŷ_t < 0`), with `S < 0` INFLATIONARY; in either case local uniqueness fails, so the
  Taylor principle is necessary also on its boundary (whenever `S ≠ 0`).
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergCentre

open Filter Topology
open NonlinearRotemberg NonlinearRotembergCentreLocal NonlinearRotembergCentreSecond
open NonlinearRotembergCentreChart NonlinearRotembergCentreTools
open NonlinearRotembergBoundaryPair (Lf kc)

variable {p : Par}

/-- Woodford (2003), App. A.3: `s = ±1` gives `s² = 1`. -/
theorem s_sq {s : ℝ} (hs : s = 1 ∨ s = -1) : s * s = 1 := by
  rcases hs with h | h <;> subst h <;> norm_num

/-- Woodford (2003), App. A.3: `|s| = 1`. -/
theorem abs_s {s : ℝ} (hs : s = 1 ∨ s = -1) : |s| = 1 := by
  rcases hs with h | h <;> subst h <;> norm_num

set_option maxHeartbeats 1000000 in
-- the choice of all constants of the argument
/-- Woodford (2003), Prop. 4.3 and App. A.3 (**the constants of the centre argument**): with
`s = ±1` and `sq > 0`, there are `δ, Λ, K, M > 0` and `η, C ≥ 0` with the smallness conditions
of `NonlinearRotembergCentreTools.cone_bound` and, for every `x` on the resource manifold with
`‖x‖ ≤ δ`: `|D|, |E| ≤ η(|L| + |V|)`, `sD ≥ (3/4)sqL² − C|V|(|L| + |V|)`,
`‖x‖ ≤ K(|L| + |V|)`, and in the cone `|V| ≤ Λ|L|`, `sL < 0 ⇒ sπ < 0 ∧ sŷ < 0`. -/
theorem setup (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hsq : 0 < s * qc p) :
    ∃ δ > 0, ∃ Λ > 0, ∃ K > 0, ∃ M > 0, ∃ η ≥ 0, ∃ C ≥ 0,
      Λ ≤ 1 ∧ C * Λ * (1 + Λ) ≤ s * qc p / 4 ∧
      η * (1 + 1 / Λ) + |p.ψ * Th p| / M ≤ (mu p - 1) / 2 ∧
      η * (Λ + 1) + Λ / M ≤ (mu p - 1) / 2 ∧ η * (1 + Λ) ≤ 1 / 2 ∧
      η * (1 + Λ) < (mu p - 1) * Λ ∧
      ∀ z : Fin 3 → ℝ, ‖z‖ ≤ δ → Res p z →
        |Dfun p z| ≤ η * (|Lf p z| + |Vf p z|) ∧ |Efun p z| ≤ η * (|Lf p z| + |Vf p z|) ∧
        3 / 4 * (s * qc p) * Lf p z ^ 2 - C * |Vf p z| * (|Lf p z| + |Vf p z|) ≤
          s * Dfun p z ∧
        ‖z‖ ≤ K * (|Lf p z| + |Vf p z|) ∧
        (|Vf p z| ≤ Λ * |Lf p z| → s * Lf p z < 0 → s * z 1 < 0 ∧ s * z 0 < 0) := by
  have hT := Th_pos hp
  have hG := Gam_pos hp
  have hσ := hp.σ_pos
  have hψ := hp.ψ_pos
  have hβ1 : 0 < 1 - p.β := by linarith [hp.β_lt_one]
  have hμ := one_lt_mu hp
  have hμ1 : 0 < mu p - 1 := by linarith
  have hss := s_sq hs
  have has := abs_s hs
  set sq := s * qc p with hsqd
  obtain ⟨ρK, hρK, K, hK, hnorm⟩ := norm_le_LV hp
  obtain ⟨ρD, hρD, C, hC, hD2⟩ := second_order_D hp hb (by positivity : 0 < sq / 4)
  set ε := min (p.ψ * Th p / 4) ((1 - p.β) * p.σ * p.ψ ^ 2 * Th p / (4 * Gam p)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  set Λ := min (min 1 (sq / (8 * (C + 1)))) (ε / 2) with hΛ
  have hΛ0 : 0 < Λ := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hΛ1 : Λ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hΛq : Λ ≤ sq / (8 * (C + 1)) := (min_le_left _ _).trans (min_le_right _ _)
  have hΛε : Λ ≤ ε / 2 := min_le_right _ _
  set M := 4 * (p.ψ * Th p + 1) / (mu p - 1) with hM
  have hM0 : 0 < M := by positivity
  set ηc := min (1 / (2 * (1 + Λ))) ((mu p - 1) * Λ / (4 * (1 + Λ))) with hηc
  have hηc0 : 0 < ηc := lt_min (by positivity) (by positivity)
  obtain ⟨ρE, hρE, hDE⟩ := rem_DE hp hb (by positivity : 0 < ηc / K)
  set η2 := min (ε / 2) (1 / 4) / (K * (1 + Λ)) with hη2
  have hη20 : 0 < η2 := by positivity
  obtain ⟨ρ2, hρ2, hLV⟩ := rem_LV hp hη20
  set δ := min (min ρK ρD) (min ρE ρ2) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨δ, hδ0, Λ, hΛ0, K, hK, M, hM0, ηc, hηc0.le, C, hC, hΛ1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc C * Λ * (1 + Λ) ≤ C * Λ * 2 := by gcongr; linarith
      _ ≤ C * (sq / (8 * (C + 1))) * 2 := by gcongr
      _ ≤ sq / 4 := by
          rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  · have h1 : ηc * (1 + 1 / Λ) ≤ (mu p - 1) / 4 := by
      have : ηc ≤ (mu p - 1) * Λ / (4 * (1 + Λ)) := min_le_right _ _
      calc ηc * (1 + 1 / Λ) ≤ (mu p - 1) * Λ / (4 * (1 + Λ)) * (1 + 1 / Λ) := by gcongr
        _ = (mu p - 1) / 4 := by field_simp; ring
    have h2 : |p.ψ * Th p| / M ≤ (mu p - 1) / 4 := by
      rw [abs_of_pos (by positivity), hM, div_div_eq_mul_div, div_le_div_iff₀ (by positivity)
        (by norm_num)]
      have : 0 < mu p - 1 := by linarith
      nlinarith
    linarith
  · have h1 : ηc * (Λ + 1) ≤ (mu p - 1) / 4 := by
      have : ηc ≤ (mu p - 1) * Λ / (4 * (1 + Λ)) := min_le_right _ _
      calc ηc * (Λ + 1) ≤ (mu p - 1) * Λ / (4 * (1 + Λ)) * (Λ + 1) := by gcongr
        _ = (mu p - 1) * Λ / 4 := by field_simp; ring
        _ ≤ (mu p - 1) / 4 := by gcongr; nlinarith
    have h2 : Λ / M ≤ (mu p - 1) / 4 := by
      rw [hM, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 0 < mu p - 1 := by linarith
      nlinarith [mul_nonneg hψ.le hT.le]
    linarith
  · have : ηc ≤ 1 / (2 * (1 + Λ)) := min_le_left _ _
    calc ηc * (1 + Λ) ≤ 1 / (2 * (1 + Λ)) * (1 + Λ) := by gcongr
      _ = 1 / 2 := by field_simp
  · have : ηc ≤ (mu p - 1) * Λ / (4 * (1 + Λ)) := min_le_right _ _
    have hm : 0 < (mu p - 1) * Λ := mul_pos (by linarith) hΛ0
    calc ηc * (1 + Λ) ≤ (mu p - 1) * Λ / (4 * (1 + Λ)) * (1 + Λ) := by gcongr
      _ = (mu p - 1) * Λ / 4 := by field_simp
      _ < (mu p - 1) * Λ := by linarith
  · intro z hz hres
    have hzK : ‖z‖ < ρK := by
      have := (min_le_left (min ρK ρD) (min ρE ρ2)).trans (min_le_left ρK ρD); linarith
    have hzD : ‖z‖ < ρD := by
      have := (min_le_left (min ρK ρD) (min ρE ρ2)).trans (min_le_right ρK ρD); linarith
    have hzE : ‖z‖ < ρE := by
      have := (min_le_right (min ρK ρD) (min ρE ρ2)).trans (min_le_left ρE ρ2); linarith
    have hz2 : ‖z‖ < ρ2 := by
      have := (min_le_right (min ρK ρD) (min ρE ρ2)).trans (min_le_right ρE ρ2); linarith
    set L := Lf p z
    set V := Vf p z
    have hn := hnorm z hzK hres
    have hX : 0 ≤ |L| + |V| := by positivity
    obtain ⟨d1, d2⟩ := hDE z hzE hres
    have hηK : ηc / K * ‖z‖ ≤ ηc * (|L| + |V|) := by
      calc ηc / K * ‖z‖ ≤ ηc / K * (K * (|L| + |V|)) := by gcongr
        _ = ηc * (|L| + |V|) := by field_simp
    refine ⟨d1.trans hηK, d2.trans hηK, ?_, hn, ?_⟩
    · have h := hD2 z hzD hres
      have e : s * Dfun p z - sq * L ^ 2 = s * (Dfun p z - qc p * L ^ 2) := by
        simp only [hsqd]; ring
      have h' : |s * (Dfun p z - qc p * L ^ 2)| ≤ sq / 4 * L ^ 2 + C * |V| * (|L| + |V|) := by
        rw [abs_mul, has, one_mul]; exact h
      have := neg_abs_le (s * (Dfun p z - qc p * L ^ 2))
      have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
      nlinarith
    · intro hcone hsL
      have hL0 : 0 < |L| := by
        have : s * L ≠ 0 := hsL.ne
        rw [abs_pos]; intro h; exact this (by rw [h, mul_zero])
      have hsLabs : s * L = -|L| := by
        have h1 : |s * L| = |L| := by rw [abs_mul, has, one_mul]
        rw [abs_of_neg hsL] at h1; linarith
      have hzL : ‖z‖ ≤ K * (1 + Λ) * |L| := by
        calc ‖z‖ ≤ K * (|L| + |V|) := hn
          _ ≤ K * (|L| + Λ * |L|) := by gcongr
          _ = K * (1 + Λ) * |L| := by ring
      obtain ⟨r1, r2⟩ := hLV z hz2 hres
      have hη2K : η2 * ‖z‖ ≤ min (ε / 2) (1 / 4) * |L| := by
        calc η2 * ‖z‖ ≤ η2 * (K * (1 + Λ) * |L|) := by gcongr
          _ = min (ε / 2) (1 / 4) * |L| := by simp only [hη2]; field_simp
      have hm1 : min (ε / 2) (1 / 4) ≤ ε / 2 := min_le_left _ _
      have hm2 : min (ε / 2) (1 / 4) ≤ 1 / 4 := min_le_right _ _
      have hLl : |Ll p z - L| ≤ |L| / 4 := by
        rw [abs_sub_comm]; nlinarith [abs_nonneg L]
      have hVl : |Vl p z| ≤ ε * |L| := by
        have := abs_sub_abs_le_abs_sub (Vl p z) V
        rw [abs_sub_comm] at this
        nlinarith [abs_nonneg L]
      -- the identities of the linear coordinates
      have iL : Th p * Ll p z = Gam p * z 1 + p.σ * vv p z := by
        simp only [Ll, Gam, vv, kc, Th]; ring
      have iV : Vl p z = p.σ * p.ψ * vv p z := by simp only [Vl, vv]; ring
      have iy : Th p * z 0 = (1 - p.β) * p.ψ * z 1 + vv p z := by simp only [vv]; ring
      have hεψ : ε ≤ p.ψ * Th p / 4 := min_le_left _ _
      have hεy : ε ≤ (1 - p.β) * p.σ * p.ψ ^ 2 * Th p / (4 * Gam p) := min_le_right _ _
      -- `Γπ − ΘL` is at most `Θ|L|/2`
      have hvv : |vv p z| ≤ ε * |L| / (p.σ * p.ψ) := by
        rw [le_div_iff₀ (by positivity)]
        have : |Vl p z| = p.σ * p.ψ * |vv p z| := by
          rw [iV, abs_mul, abs_of_pos (by positivity : 0 < p.σ * p.ψ)]
        linarith
      have hgap : |Gam p * z 1 - Th p * L| ≤ Th p / 2 * |L| := by
        have e : Gam p * z 1 - Th p * L = Th p * (Ll p z - L) - Vl p z / p.ψ := by
          have : Vl p z / p.ψ = p.σ * vv p z := by rw [iV]; field_simp
          rw [this]; linear_combination (-1) * iL
        rw [e]
        have a1 : |Th p * (Ll p z - L)| ≤ Th p * (|L| / 4) := by
          rw [abs_mul, abs_of_pos hT]; exact mul_le_mul_of_nonneg_left hLl hT.le
        have a2 : |Vl p z / p.ψ| ≤ Th p / 4 * |L| := by
          rw [abs_div, abs_of_pos hψ, div_le_iff₀ hψ]
          calc |Vl p z| ≤ ε * |L| := hVl
            _ ≤ p.ψ * Th p / 4 * |L| := by gcongr
            _ = _ := by ring
        calc _ ≤ |Th p * (Ll p z - L)| + |Vl p z / p.ψ| := abs_sub _ _
          _ ≤ Th p * (|L| / 4) + Th p / 4 * |L| := add_le_add a1 a2
          _ = Th p / 2 * |L| := by ring
      have hspi : s * (Gam p * z 1) ≤ -(Th p / 2 * |L|) := by
        have h1 : |s * (Gam p * z 1 - Th p * L)| ≤ Th p / 2 * |L| := by
          rw [abs_mul, has, one_mul]; exact hgap
        have h2 := le_abs_self (s * (Gam p * z 1 - Th p * L))
        have e : s * (Gam p * z 1) = Th p * (s * L) + s * (Gam p * z 1 - Th p * L) := by ring
        rw [e, hsLabs]
        nlinarith
      have hpi : s * z 1 < 0 := by
        have : s * (Gam p * z 1) = Gam p * (s * z 1) := by ring
        rw [this] at hspi
        have : Gam p * (s * z 1) < 0 := lt_of_le_of_lt hspi (by
          have := mul_pos hT hL0; linarith)
        exact neg_of_mul_neg_right this hG.le
      refine ⟨hpi, ?_⟩
      -- the output gap has the sign of inflation
      have hpiabs : Th p / 2 * |L| ≤ Gam p * |z 1| := by
        have h1 : |s * z 1| = |z 1| := by rw [abs_mul, has, one_mul]
        have : -(s * (Gam p * z 1)) ≤ |s * (Gam p * z 1)| := neg_le_abs _
        rw [show s * (Gam p * z 1) = Gam p * (s * z 1) by ring, abs_mul, abs_of_pos hG, h1]
          at this
        rw [show s * (Gam p * z 1) = Gam p * (s * z 1) by ring] at hspi
        linarith
      have hsy : s * (Th p * z 0) < 0 := by
        rw [iy]
        have hs1 : s * z 1 = -|z 1| := by
          have h1 : |s * z 1| = |z 1| := by rw [abs_mul, has, one_mul]
          rw [abs_of_neg hpi] at h1; linarith
        have hv1 : s * vv p z ≤ |vv p z| := by
          have := le_abs_self (s * vv p z); rw [abs_mul, has, one_mul] at this; exact this
        have hvsmall : |vv p z| < (1 - p.β) * p.ψ * |z 1| := by
          have hz1 : Th p * |L| / (2 * Gam p) ≤ |z 1| := by
            rw [div_le_iff₀ (by positivity)]; linarith
          calc |vv p z| ≤ ε * |L| / (p.σ * p.ψ) := hvv
            _ ≤ (1 - p.β) * p.σ * p.ψ ^ 2 * Th p / (4 * Gam p) * |L| / (p.σ * p.ψ) := by
                gcongr
            _ = (1 - p.β) * p.ψ * (Th p * |L| / (2 * Gam p)) / 2 := by field_simp; ring
            _ < (1 - p.β) * p.ψ * (Th p * |L| / (2 * Gam p)) := by
                have : 0 < (1 - p.β) * p.ψ * (Th p * |L| / (2 * Gam p)) := by positivity
                linarith
            _ ≤ (1 - p.β) * p.ψ * |z 1| := by gcongr
        have e : s * ((1 - p.β) * p.ψ * z 1 + vv p z) =
            (1 - p.β) * p.ψ * (s * z 1) + s * vv p z := by ring
        rw [e, hs1]
        linarith
      have : Th p * (s * z 0) < 0 := by linarith [show s * (Th p * z 0) = Th p * (s * z 0) by ring]
      exact neg_of_mul_neg_right this hT.le

/-- Woodford (2003), App. A.3: `L(0) = 0`. -/
theorem Lf_zero : Lf p 0 = 0 := by simp [Lf, Gadj]

/-! ## No equilibrium on the wrong side -/

/-- Woodford (2003), Prop. 4.3 and App. A.3 (**the boundary equilibria are one-sided**): with
`s = ±1` and `sq > 0`, there is `δ > 0` such that every exact perfect-foresight equilibrium
(no disturbances) with `‖x_t‖ ≤ δ` at every date has `sL_t ≤ 0` at every date, `sL_t`
nondecreasing, `x_t → 0`, and — unless `x₀ = 0` — `sπ_t < 0` and `sŷ_t < 0` at EVERY date. -/
theorem one_sided (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hsq : 0 < s * qc p) :
    ∃ δ > 0, ∀ z : ℕ → Fin 3 → ℝ, PFEq p 0 z → (∀ t, ‖z t‖ ≤ δ) →
      (∀ t, s * Lf p (z t) ≤ 0) ∧ Monotone (fun t => s * Lf p (z t)) ∧
      Tendsto z atTop (𝓝 0) ∧ (z 0 ≠ 0 → ∀ t, s * z t 1 < 0 ∧ s * z t 0 < 0) := by
  obtain ⟨δ, hδ, Λ, hΛ, K, hK, M, hM, η, hη, C, hC, hΛ1, hCΛ, h1, h2, h3, -, hest⟩ :=
    setup hp hb hs hsq
  obtain ⟨ρ', hρ', K', hK', hLV⟩ := LV_le_norm hp
  have has := abs_s hs
  have hss := s_sq hs
  refine ⟨min δ (ρ' / 2), by positivity, fun z hz hzb => ?_⟩
  have hzδ : ∀ t, ‖z t‖ ≤ δ := fun t => (hzb t).trans (min_le_left _ _)
  have hzρ : ∀ t, ‖z t‖ < ρ' := fun t => by
    have := (hzb t).trans (min_le_right _ _); linarith
  have hres : ∀ t, Res p (z t) := fun t => (pf_components hz t).2.2
  set L : ℕ → ℝ := fun t => Lf p (z t) with hLdef
  set V : ℕ → ℝ := fun t => Vf p (z t) with hVdef
  have hrec := fun t => exact_rec hp hz t
  have hE := fun t => (hest (z t) (hzδ t) (hres t))
  have hVb : ∀ t, |V t| ≤ K' * δ := fun t =>
    ((hLV (z t) (hzρ t)).2).trans (mul_le_mul_of_nonneg_left (hzδ t) hK'.le)
  have hLb : ∀ t, |L t| ≤ K' * δ := fun t =>
    ((hLV (z t) (hzρ t)).1).trans (mul_le_mul_of_nonneg_left (hzδ t) hK'.le)
  -- the cone
  have hcone : ∀ t, |V t| ≤ Λ * |L t| := by
    intro t
    have := cone_bound (ν := 0) (c := p.ψ * Th p) (L := L) (V := V)
      (D := fun t => Dfun p (z t)) (E := fun t => Efun p (z t)) (one_lt_mu hp) hΛ hM hη h1 h2
      (fun t => by simp only [hLdef]; rw [(hrec t).1])
      (fun t => by simp only [hVdef]; rw [(hrec t).2])
      (fun t => (hE t).1) (fun t => (hE t).2.1) hVb t
    simpa using this
  -- the drift in the cone
  have hdrift : ∀ t, s * qc p / 2 * (s * L t) ^ 2 ≤ s * Dfun p (z t) := by
    intro t
    have hq := (hE t).2.2.1
    have hc := hcone t
    have hL2 : (s * L t) ^ 2 = L t ^ 2 := by
      rw [mul_pow, show s ^ 2 = 1 by rw [sq]; exact hss, one_mul]
    rw [hL2]
    have hb1 : C * |V t| * (|L t| + |V t|) ≤ C * (Λ * |L t|) * (|L t| + Λ * |L t|) := by
      gcongr
    have hb2 : C * (Λ * |L t|) * (|L t| + Λ * |L t|) = C * Λ * (1 + Λ) * L t ^ 2 := by
      rw [← sq_abs (L t)]; ring
    have hb3 : C * Λ * (1 + Λ) * L t ^ 2 ≤ s * qc p / 4 * L t ^ 2 :=
      mul_le_mul_of_nonneg_right hCΛ (sq_nonneg _)
    have : 0 ≤ s * qc p / 4 * L t ^ 2 := by positivity
    nlinarith
  have hLs : ∀ t, s * L (t + 1) = s * L t + s * Dfun p (z t) := fun t => by
    simp only [hLdef]; rw [(hrec t).1]; ring
  have hLsb : ∀ t, |s * L t| ≤ K' * δ := fun t => by rw [abs_mul, has, one_mul]; exact hLb t
  have hq2 : 0 < s * qc p / 2 := by positivity
  have hnp := centre_nonpos hq2 hLs hdrift hLsb
  obtain ⟨hmono, htend⟩ := centre_tendsto hq2 hLs hdrift hLsb
  refine ⟨hnp, hmono, ?_, ?_⟩
  · -- `x_t → 0`
    have hLt : Tendsto L atTop (𝓝 0) := by
      have := htend.const_mul s
      simp only [mul_zero] at this
      refine this.congr fun t => ?_
      rw [← mul_assoc, hss, one_mul]
    have hbound : ∀ t, ‖z t‖ ≤ K * (1 + Λ) * |L t| := fun t => by
      have := (hE t).2.2.2.1
      calc ‖z t‖ ≤ K * (|L t| + |V t|) := this
        _ ≤ K * (|L t| + Λ * |L t|) := by gcongr; exact hcone t
        _ = K * (1 + Λ) * |L t| := by ring
    have hlim : Tendsto (fun t => K * (1 + Λ) * |L t|) atTop (𝓝 0) := by
      have := (hLt.abs).const_mul (K * (1 + Λ))
      simpa using this
    exact squeeze_zero_norm hbound hlim
  · -- the signs, unless `x₀ = 0`
    intro hz0 t
    have hL0 : s * L 0 < 0 := by
      rcases (hnp 0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hL : L 0 = 0 := by
          have : s * (s * L 0) = 0 := by rw [h, mul_zero]
          rwa [← mul_assoc, hss, one_mul] at this
        have hV : V 0 = 0 := by
          have := hcone 0; rw [hL, abs_zero, mul_zero] at this; exact abs_nonpos_iff.1 this
        have := (hE 0).2.2.2.1
        simp only [hLdef, hVdef] at hL hV
        rw [hL, hV, abs_zero, add_zero, mul_zero] at this
        exact hz0 (norm_le_zero_iff.1 this)
    have hDh : ∀ t, |s * Dfun p (z t)| ≤ |s * L t| / 2 := fun t => by
      rw [abs_mul, has, one_mul, abs_mul s, has, one_mul]
      calc |Dfun p (z t)| ≤ η * (|L t| + |V t|) := (hE t).1
        _ ≤ η * (|L t| + Λ * |L t|) := by gcongr; exact hcone t
        _ = η * (1 + Λ) * |L t| := by ring
        _ ≤ 1 / 2 * |L t| := by gcongr
        _ = |L t| / 2 := by ring
    have hneg := centre_neg_of_neg hLs hDh hL0 t
    exact (hE t).2.2.2.2 (hcone t) hneg

/-! ## The continuum on the right side -/

/-- Woodford (2003), App. A.3: The reflection `(L, V) ↦ (sL, V)`. -/
def flipS (s : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (s * q.1, q.2)

/-- Woodford (2003), App. A.3: The reflected forward map `T_s = flip ∘ Tm ∘ flip`. -/
noncomputable def Ts (p : Par) (s : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := flipS s (Tm p 0 (flipS s q))

/-- Woodford (2003), App. A.3: `Tmⁿ ∘ flip = flip ∘ T_sⁿ`. -/
theorem iterate_Ts {s : ℝ} (hs : s = 1 ∨ s = -1) (q : ℝ × ℝ) (n : ℕ) :
    (Tm p 0)^[n] (flipS s q) = flipS s ((Ts p s)^[n] q) := by
  have hss := s_sq hs
  have hff : ∀ w : ℝ × ℝ, flipS s (flipS s w) = w := fun w => by
    simp only [flipS]; rw [← mul_assoc, hss, one_mul]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', Ts, hff]

/-- Woodford (2003), App. A.3: `‖flip q‖ = ‖q‖`. -/
theorem norm_flipS {s : ℝ} (hs : s = 1 ∨ s = -1) (q : ℝ × ℝ) : ‖flipS s q‖ = ‖q‖ := by
  simp only [flipS, Prod.norm_def, Real.norm_eq_abs, abs_mul, abs_s hs, one_mul]

set_option maxHeartbeats 1000000 in
-- the verification of the Ważewski hypotheses
/-- Woodford (2003), Prop. 4.3 and App. A.3 (**the continuum of boundary equilibria**): with
`s = ±1` and `sq > 0`, for every `r > 0` there is `c₀ > 0` such that for every `c ∈ (0, c₀]` there
is an exact perfect-foresight equilibrium (no disturbances) with `L_0 = −sc`, `‖x_t‖ ≤ r` at
every date, `x_t → 0`, and `sπ_t < 0`, `sŷ_t < 0` at every date. -/
theorem continuum (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hsq : 0 < s * qc p) :
    ∀ r > 0, ∃ c0 > 0, ∀ c, 0 < c → c ≤ c0 → ∃ z : ℕ → Fin 3 → ℝ, PFEq p 0 z ∧
      Lf p (z 0) = -(s * c) ∧ (∀ t, ‖z t‖ ≤ r) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ t, s * z t 1 < 0 ∧ s * z t 0 < 0 := by
  intro r hr
  obtain ⟨δ, hδ, Λ, hΛ, K, hK, M, hM, η, hη, C, hC, hΛ1, hCΛ, -, -, h3, h4, hest⟩ :=
    setup hp hb hs hsq
  obtain ⟨δo, hδo, hos⟩ := one_sided hp hb hs hsq
  obtain ⟨ρc, hρc, hdomc, hcont, htend⟩ := chart_local (p := p)
  have has := abs_s hs
  have hss := s_sq hs
  set εr := min (min δ δo) r with hεr
  have hεr0 : 0 < εr := lt_min (lt_min hδ hδo) hr
  obtain ⟨ρz, hρz, hball⟩ := Metric.eventually_nhds_iff.1
    (htend.eventually (Metric.ball_mem_nhds (0 : Fin 3 → ℝ) hεr0))
  set ℓ0 := min ρc ρz / 2 with hℓ0
  have hℓ00 : 0 < ℓ0 := by positivity
  refine ⟨ℓ0, hℓ00, fun c hc hcl => ?_⟩
  -- points of the cone are in the chart and small
  have hR : ∀ q ∈ coneR ℓ0 Λ, ‖flipS s q‖ < ρc ∧ ‖Zc p (flipS s q)‖ < εr := by
    intro q hq
    have hq1 : |q.1| ≤ ℓ0 := by rw [abs_le]; exact ⟨hq.1, by linarith [hq.2.1]⟩
    have hq2 : |q.2| ≤ ℓ0 := hq.2.2.trans (by nlinarith [abs_nonneg q.1])
    have hn : ‖flipS s q‖ ≤ ℓ0 := by
      rw [norm_flipS hs, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact max_le hq1 hq2
    have hl1 : ℓ0 < ρc := by have := min_le_left ρc ρz; linarith
    have hl2 : ℓ0 < ρz := by have := min_le_right ρc ρz; linarith
    refine ⟨hn.trans_lt hl1, ?_⟩
    have := hball (show dist (flipS s q) 0 < ρz by rw [dist_zero_right]; linarith)
    simpa [dist_zero_right] using this
  -- the properties at a point of the cone
  have hpt : ∀ q ∈ coneR ℓ0 Λ, Res p (Zc p (flipS s q)) ∧
      Lf p (Zc p (flipS s q)) = s * q.1 ∧ Vf p (Zc p (flipS s q)) = q.2 ∧
      Ts p s q = (q.1 + s * Dfun p (Zc p (flipS s q)),
        mu p * q.2 + Efun p (Zc p (flipS s q))) := by
    intro q hq
    obtain ⟨h1, h2, h3⟩ := Zc_spec hp (hdomc _ (hR q hq).1)
    refine ⟨h1, h2, h3, ?_⟩
    change flipS s (Tm p 0 (flipS s q)) = _
    rw [Tm_eq hp 0, h2, h3]
    simp only [flipS]
    ext
    · simp only [mul_add, ← mul_assoc, hss, one_mul, add_zero]
    · simp
  have hDE : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 →
      |Dfun p (Zc p (flipS s q))| ≤ η * (1 + Λ) * |q.1| ∧
      |Efun p (Zc p (flipS s q))| ≤ η * (1 + Λ) * |q.1| ∧
      s * qc p / 2 * q.1 ^ 2 ≤ s * Dfun p (Zc p (flipS s q)) := by
    intro q hq _
    obtain ⟨h1, h2, h3, -⟩ := hpt q hq
    have hz := (hR q hq).2
    have hzδ : ‖Zc p (flipS s q)‖ ≤ δ := by
      have := min_le_left (min δ δo) r; have := min_le_left δ δo; linarith
    obtain ⟨e1, e2, e3, -, -⟩ := hest (Zc p (flipS s q)) hzδ h1
    rw [h2, h3, abs_mul, has, one_mul] at e1 e2 e3
    have hc2 := hq.2.2
    have hsq2 : (s * q.1) ^ 2 = q.1 ^ 2 := by
      rw [mul_pow, show s ^ 2 = 1 by rw [sq]; exact hss, one_mul]
    rw [hsq2] at e3
    have hX : |q.1| + |q.2| ≤ (1 + Λ) * |q.1| := by linarith
    refine ⟨?_, ?_, ?_⟩
    · calc _ ≤ η * (|q.1| + |q.2|) := e1
        _ ≤ η * ((1 + Λ) * |q.1|) := by gcongr
        _ = _ := by ring
    · calc _ ≤ η * (|q.1| + |q.2|) := e2
        _ ≤ η * ((1 + Λ) * |q.1|) := by gcongr
        _ = _ := by ring
    · have hb1 : C * |q.2| * (|q.1| + |q.2|) ≤ C * (Λ * |q.1|) * ((1 + Λ) * |q.1|) := by
        gcongr
      have hb2 : C * (Λ * |q.1|) * ((1 + Λ) * |q.1|) = C * Λ * (1 + Λ) * q.1 ^ 2 := by
        rw [← sq_abs q.1]; ring
      have hb3 : C * Λ * (1 + Λ) * q.1 ^ 2 ≤ s * qc p / 4 * q.1 ^ 2 :=
        mul_le_mul_of_nonneg_right hCΛ (sq_nonneg _)
      have : 0 ≤ s * qc p / 4 * q.1 ^ 2 := by positivity
      nlinarith
  -- the Ważewski hypotheses
  have hT2 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.1 ≤ (Ts p s q).1 ∧ (Ts p s q).1 < 0 := by
    intro q hq hq1
    obtain ⟨a1, -, a3⟩ := hDE q hq hq1
    rw [(hpt q hq).2.2.2]
    have hsD := neg_abs_le (s * Dfun p (Zc p (flipS s q)))
    rw [abs_mul, has, one_mul] at hsD
    have hq1' : |q.1| = -q.1 := abs_of_neg hq1
    have : 0 ≤ s * qc p / 2 * q.1 ^ 2 := by positivity
    have hle : s * Dfun p (Zc p (flipS s q)) ≤ |Dfun p (Zc p (flipS s q))| := by
      have := le_abs_self (s * Dfun p (Zc p (flipS s q)))
      rwa [abs_mul, has, one_mul] at this
    constructor
    · change q.1 ≤ q.1 + s * Dfun p (Zc p (flipS s q)); linarith
    · change q.1 + s * Dfun p (Zc p (flipS s q)) < 0
      nlinarith [mul_le_mul_of_nonneg_right h3 (abs_nonneg q.1)]
  have hT3 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.2 = Λ * |q.1| →
      Λ * |(Ts p s q).1| < (Ts p s q).2 := by
    intro q hq hq1 hside
    obtain ⟨-, a2, -⟩ := hDE q hq hq1
    obtain ⟨b1, b2⟩ := hT2 q hq hq1
    have habs : |(Ts p s q).1| ≤ |q.1| := by
      rw [abs_of_neg b2, abs_of_neg hq1]; linarith
    rw [(hpt q hq).2.2.2] at habs ⊢
    have hE := neg_abs_le (Efun p (Zc p (flipS s q)))
    have hpos : 0 < |q.1| := abs_pos.2 hq1.ne
    have key : η * (1 + Λ) * |q.1| < (mu p - 1) * Λ * |q.1| :=
      mul_lt_mul_of_pos_right h4 hpos
    change Λ * |q.1 + s * Dfun p (Zc p (flipS s q))| <
      mu p * q.2 + Efun p (Zc p (flipS s q))
    rw [hside]
    nlinarith [mul_le_mul_of_nonneg_left habs hΛ.le]
  have hT4 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.2 = -(Λ * |q.1|) →
      (Ts p s q).2 < -(Λ * |(Ts p s q).1|) := by
    intro q hq hq1 hside
    obtain ⟨-, a2, -⟩ := hDE q hq hq1
    obtain ⟨b1, b2⟩ := hT2 q hq hq1
    have habs : |(Ts p s q).1| ≤ |q.1| := by
      rw [abs_of_neg b2, abs_of_neg hq1]; linarith
    rw [(hpt q hq).2.2.2] at habs ⊢
    have hE := le_abs_self (Efun p (Zc p (flipS s q)))
    have hpos : 0 < |q.1| := abs_pos.2 hq1.ne
    have key : η * (1 + Λ) * |q.1| < (mu p - 1) * Λ * |q.1| :=
      mul_lt_mul_of_pos_right h4 hpos
    change mu p * q.2 + Efun p (Zc p (flipS s q)) <
      -(Λ * |q.1 + s * Dfun p (Zc p (flipS s q))|)
    rw [hside]
    nlinarith [mul_le_mul_of_nonneg_left habs hΛ.le]
  have hTc : ContinuousOn (Ts p s) (coneR ℓ0 Λ) := by
    have hf : Continuous (flipS s) := by unfold flipS; fun_prop
    have hmaps : Set.MapsTo (flipS s) (coneR ℓ0 Λ) (Metric.ball 0 ρc) := fun q hq => by
      simpa [dist_zero_right] using (hR q hq).1
    exact hf.comp_continuousOn ((continuousOn_Tm hcont 0).comp hf.continuousOn hmaps)
  obtain ⟨V0, -, horb⟩ := wazewski hΛ hTc hT2 hT3 hT4 (L0 := -c) (by linarith) (by linarith)
  -- the equilibrium
  set q0 : ℝ × ℝ := flipS s (-c, V0) with hq0
  have hdom : ∀ t, Dom p ((Tm p 0)^[t] q0) := fun t => by
    rw [hq0, iterate_Ts hs]; exact hdomc _ (hR _ (horb t)).1
  have heq := orbit_pfeq hp 0 q0 hdom
  set z : ℕ → Fin 3 → ℝ := fun t => Zc p ((Tm p 0)^[t] q0) with hz
  have hzsmall : ∀ t, ‖z t‖ < εr := fun t => by
    simp only [hz]; rw [hq0, iterate_Ts hs]; exact (hR _ (horb t)).2
  have hL0 : Lf p (z 0) = -(s * c) := by
    have := (Zc_spec hp (hdom 0)).2.1
    simp only [hz] at this ⊢
    rw [this]; simp [hq0, flipS]
  have hzδo : ∀ t, ‖z t‖ ≤ δo := fun t => by
    have := hzsmall t; have := min_le_right δ δo; have := min_le_left (min δ δo) r; linarith
  obtain ⟨-, -, hlim, hsign⟩ := hos z heq hzδo
  have hz0 : z 0 ≠ 0 := by
    intro h
    rw [h, Lf_zero] at hL0
    have : s * c ≠ 0 := mul_ne_zero (by rcases hs with h | h <;> rw [h] <;> norm_num) hc.ne'
    exact this (by linarith)
  refine ⟨z, heq, hL0, fun t => ?_, hlim, hsign hz0⟩
  have := hzsmall t; have := min_le_right (min δ δo) r; linarith

/-! ## The answer on the boundary -/

/-- Woodford (2003), Prop. 4.3 and App. A.3 (**`S > 0`: a DEFLATIONARY one-sided continuum**): on
the boundary `κ(φ_π − 1) + (1 − β)φ_y = 0` with `φ_y > 0`, if
`S = σ(θm)² + 3(1−β)θm − (1−β)²ψ > 0` then
(1) for every `r > 0` there is `c₀ > 0` such that every `c ∈ (0, c₀]` gives an exact
perfect-foresight equilibrium with `L_0 = −c` (distinct `c`, distinct equilibria), `‖x_t‖ ≤ r`,
`x_t → 0`, and deflation `π_t < 0` with a negative output gap `ŷ_t < 0` at every date; and
(2) there is `δ > 0` such that every equilibrium with `‖x_t‖ ≤ δ` converges to the steady state
and, unless it is the steady state, has `π_t < 0` and `ŷ_t < 0` at every date: there is no
inflationary equilibrium near the steady state. -/
theorem deflationary (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (hφy : 0 < p.φy) (hS : 0 < Sc p) :
    (∀ r > 0, ∃ c0 > 0, ∀ c, 0 < c → c ≤ c0 → ∃ z : ℕ → Fin 3 → ℝ, PFEq p 0 z ∧
      Lf p (z 0) = -c ∧ (∀ t, ‖z t‖ ≤ r) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ t, z t 1 < 0 ∧ z t 0 < 0) ∧
    ∃ δ > 0, ∀ z : ℕ → Fin 3 → ℝ, PFEq p 0 z → (∀ t, ‖z t‖ ≤ δ) →
      Tendsto z atTop (𝓝 0) ∧ (z 0 ≠ 0 → ∀ t, z t 1 < 0 ∧ z t 0 < 0) := by
  have hs : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hsq : 0 < 1 * qc p := by rw [one_mul]; exact ((q_pos_iff hp hφy).1).2 hS
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨c0, hc0, h⟩ := continuum hp hb hs hsq r hr
    refine ⟨c0, hc0, fun c hc hcl => ?_⟩
    obtain ⟨z, h1, h2, h3, h4, h5⟩ := h c hc hcl
    exact ⟨z, h1, by rw [h2]; ring, h3, h4, fun t => by
      have := h5 t; simp only [one_mul] at this; exact this⟩
  · obtain ⟨δ, hδ, h⟩ := one_sided hp hb hs hsq
    refine ⟨δ, hδ, fun z hz hzb => ?_⟩
    obtain ⟨-, -, h3, h4⟩ := h z hz hzb
    exact ⟨h3, fun hz0 t => by have := h4 hz0 t; simp only [one_mul] at this; exact this⟩

/-- Woodford (2003), Prop. 4.3 and App. A.3 (**`S < 0`: an INFLATIONARY one-sided continuum**):
on the boundary with `φ_y > 0`, if `S < 0` then (1) for every `r > 0` there is `c₀ > 0` such that
every `c ∈ (0, c₀]` gives an exact perfect-foresight equilibrium with `L_0 = c`, `‖x_t‖ ≤ r`,
`x_t → 0`, and inflation `π_t > 0` with a positive output gap `ŷ_t > 0` at every date; and (2)
every equilibrium within some `δ > 0` converges and, unless it is the steady state, has `π_t > 0`
and `ŷ_t > 0` at every date. -/
theorem inflationary (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (hφy : 0 < p.φy) (hS : Sc p < 0) :
    (∀ r > 0, ∃ c0 > 0, ∀ c, 0 < c → c ≤ c0 → ∃ z : ℕ → Fin 3 → ℝ, PFEq p 0 z ∧
      Lf p (z 0) = c ∧ (∀ t, ‖z t‖ ≤ r) ∧ Tendsto z atTop (𝓝 0) ∧
      ∀ t, 0 < z t 1 ∧ 0 < z t 0) ∧
    ∃ δ > 0, ∀ z : ℕ → Fin 3 → ℝ, PFEq p 0 z → (∀ t, ‖z t‖ ≤ δ) →
      Tendsto z atTop (𝓝 0) ∧ (z 0 ≠ 0 → ∀ t, 0 < z t 1 ∧ 0 < z t 0) := by
  have hs : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have hsq : 0 < -1 * qc p := by
    have := ((q_pos_iff hp hφy).2).2 hS; linarith
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨c0, hc0, h⟩ := continuum hp hb hs hsq r hr
    refine ⟨c0, hc0, fun c hc hcl => ?_⟩
    obtain ⟨z, h1, h2, h3, h4, h5⟩ := h c hc hcl
    exact ⟨z, h1, by rw [h2]; ring, h3, h4, fun t => by
      have := h5 t; constructor <;> linarith [this.1, this.2]⟩
  · obtain ⟨δ, hδ, h⟩ := one_sided hp hb hs hsq
    refine ⟨δ, hδ, fun z hz hzb => ?_⟩
    obtain ⟨-, -, h3, h4⟩ := h z hz hzb
    exact ⟨h3, fun hz0 t => by
      have := h4 hz0 t; constructor <;> linarith [this.1, this.2]⟩

/-- Woodford (2003), Prop. 4.3 (**the Taylor principle is necessary also on its boundary**):
on the boundary with `φ_y > 0` and `S ≠ 0`, local uniqueness fails in the exact model: for every
`r > 0` there are two distinct exact perfect-foresight equilibria within `r` of the steady state
(one of them the steady state). -/
theorem not_locally_unique (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (hφy : 0 < p.φy) (hS : Sc p ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∃ z : ℕ → Fin 3 → ℝ, PFEq p 0 z ∧ (∀ t, ‖z t‖ ≤ r) ∧ z ≠ fun _ => 0 := by
  rcases lt_or_gt_of_ne hS with h | h
  · obtain ⟨c0, hc0, hc⟩ := (inflationary hp hb hφy h).1 r hr
    obtain ⟨z, h1, h2, h3, -, -⟩ := hc c0 hc0 le_rfl
    refine ⟨z, h1, h3, fun hz => ?_⟩
    rw [hz, Lf_zero] at h2; linarith
  · obtain ⟨c0, hc0, hc⟩ := (deflationary hp hb hφy h).1 r hr
    obtain ⟨z, h1, h2, h3, -, -⟩ := hc c0 hc0 le_rfl
    refine ⟨z, h1, h3, fun hz => ?_⟩
    rw [hz, Lf_zero] at h2; linarith

end Woodford.StabilizationWelfare.NonlinearRotembergCentre
