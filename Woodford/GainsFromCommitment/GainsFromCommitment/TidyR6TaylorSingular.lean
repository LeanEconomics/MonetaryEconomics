/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR5TaylorRegion

/-!
# Proposition 7.12 at the singular `(ρ_r, ρ_u)`: the rank-deficient case

Woodford (2003), *Interest and Prices*, Chapter 7, §3.2, pp. 514–515 (Proposition 7.12, the
consistency conditions for `(φ_π, φ_x)` and the remark that they determine the coefficients
"for almost all parameter values"), and footnote 33 (Taylor coefficients of any sign).

`TidyR5TaylorRegion.oni_implementable_iff` characterises exactly when the optimal noninertial
(ONI) plan is the equilibrium of a determinate Taylor rule at every `(ρ_r, ρ_u)` where the 2×2
consistency system for `(φ_π, φ_x/4)` is nonsingular. This module removes that restriction.

## Main results

* `oni_implementable_iff_exists` (**every `(ρ_r, ρ_u)`**): the ONI plan is the equilibrium of a
  determinate Taylor rule of any sign iff some `(φ_π, φ_x)` solves the consistency system and
  lies in the determinacy region.
* `iRF4_pos`: the response of the interest rate to `rⁿ` in the ONI plan is positive, so the
  `rⁿ`-row of the consistency system is never `0 = 0`.
* **The rank-deficient case** (`oni_implementable_singular_iff`): where `det G = 0` the ONI plan
  is implementable iff (i) the `rⁿ`-row `(π_r, x_r)` is nonzero, (ii) the augmented system has
  rank one (`π_u i_r = i_u π_r`, `x_u i_r = i_u x_r`), and (iii) the line of solutions meets the
  determinacy region — an explicit one-dimensional Fourier–Motzkin condition on the three affine
  functions `Δ − β`, `A`, `C` (or their negatives) along the line (`fm1_iff`, `region_line_iff`).
* `not_implementable_li_zero`: for `λ_i = 0` (singular everywhere) the ONI plan is NEVER the
  equilibrium of a Taylor rule (for non-degenerate disturbances); `not_implementable_r_row_zero`:
  the same at every `ρ_r` with `γ_r = ρ_rκσ`.
-/

namespace Woodford.GainsFromCommitment.TidyR6TaylorSingular

open Filter Topology
open OptimalTaylor (taylorDelta TaylorEqm ModelDet detG phiPiG phiXG taylorRule_plan2
  plan2_bdd_adapted plan2_of)
open Noninertial (taylorRule Nondeg2)
open VarianceFrontier (plan2 plan2_apply)
open TidyR5TaylorRegion (TaylorRegion regA regC taylor_determinate_iff_region
  taylor_determinate_iff_region_any)

/-! ### One-dimensional Fourier–Motzkin -/

/-- Woodford (2003), fn. 33, p. 515 (tool): finitely many affine functions `pᵢ + qᵢ s` of one real
variable are simultaneously positive at some `s` iff every constant one is positive and every
increasing one is below every decreasing one where they cross (`pᵢqⱼ < pⱼqᵢ`). -/
theorem fm1_iff {n : ℕ} (p q : Fin n → ℝ) :
    (∃ s : ℝ, ∀ i, 0 < p i + q i * s) ↔
      (∀ i, q i = 0 → 0 < p i) ∧ ∀ i j, 0 < q i → q j < 0 → p i * q j < p j * q i := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨fun i hi => by simpa [hi] using hs i, fun i j hi hj => ?_⟩
    have h1 := hs i
    have h2 := hs j
    nlinarith [mul_pos hi (neg_pos.mpr hj)]
  · rintro ⟨h0, hpair⟩
    set lo : Fin n → ℝ := fun i => -p i / q i with hlo
    have hpos : ∀ i s, 0 < q i → lo i < s → 0 < p i + q i * s := fun i s hi h => by
      have : -p i < q i * s := by
        have := (div_lt_iff₀ hi).mp h
        linarith
      linarith
    have hneg : ∀ i s, q i < 0 → s < lo i → 0 < p i + q i * s := fun i s hi h => by
      have : q i * s > -p i := by
        have := (lt_div_iff_of_neg hi).mp h
        linarith
      linarith
    set SL := Finset.univ.filter (fun i => 0 < q i) with hSL
    set SU := Finset.univ.filter (fun i => q i < 0) with hSU
    have hcase : ∀ i, 0 < q i ∨ q i < 0 ∨ q i = 0 := fun i => by
      rcases lt_trichotomy (q i) 0 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    by_cases hL : SL.Nonempty <;> by_cases hU : SU.Nonempty
    · set L := SL.sup' hL lo
      set U := SU.inf' hU lo
      obtain ⟨i0, hi0, hLi⟩ := Finset.exists_mem_eq_sup' hL lo
      obtain ⟨j0, hj0, hUj⟩ := Finset.exists_mem_eq_inf' hU lo
      have hi0' : 0 < q i0 := (Finset.mem_filter.mp hi0).2
      have hj0' : q j0 < 0 := (Finset.mem_filter.mp hj0).2
      have hLU : L < U := by
        change SL.sup' hL lo < SU.inf' hU lo
        rw [hLi, hUj]
        have ea : lo i0 * q i0 = -p i0 := by simp only [hlo]; field_simp
        have eb : lo j0 * q j0 = -p j0 := by
          simp only [hlo]; rw [div_mul_cancel₀ _ hj0'.ne]
        have hp := hpair i0 j0 hi0' hj0'
        have hm : 0 < q i0 * -q j0 := mul_pos hi0' (neg_pos.mpr hj0')
        by_contra hc
        push Not at hc
        have : (lo j0 - lo i0) * (q i0 * -q j0) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hm.le
        nlinarith
      refine ⟨(L + U) / 2, fun i => ?_⟩
      rcases hcase i with h | h | h
      · refine hpos i _ h ?_
        have : lo i ≤ L := Finset.le_sup' lo (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        linarith
      · refine hneg i _ h ?_
        have : U ≤ lo i := Finset.inf'_le lo (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        linarith
      · simpa [h] using h0 i h
    · set L := SL.sup' hL lo
      refine ⟨L + 1, fun i => ?_⟩
      rcases hcase i with h | h | h
      · refine hpos i _ h ?_
        have : lo i ≤ L := Finset.le_sup' lo (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        linarith
      · exact absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ hU
      · simpa [h] using h0 i h
    · set U := SU.inf' hU lo
      refine ⟨U - 1, fun i => ?_⟩
      rcases hcase i with h | h | h
      · exact absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ hL
      · refine hneg i _ h ?_
        have : U ≤ lo i := Finset.inf'_le lo (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        linarith
      · simpa [h] using h0 i h
    · refine ⟨0, fun i => ?_⟩
      rcases hcase i with h | h | h
      · exact absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ hL
      · exact absurd ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ hU
      · simpa [h] using h0 i h

/-- Woodford (2003), fn. 33, p. 515: the Fourier–Motzkin condition of `fm1_iff`. -/
def FM {n : ℕ} (p q : Fin n → ℝ) : Prop :=
  (∀ i, q i = 0 → 0 < p i) ∧ ∀ i j, 0 < q i → q j < 0 → p i * q j < p j * q i

/-! ### The determinacy region along a line -/

/-- Woodford (2003), fn. 33 and App. C.2: the constant terms of `(Δ − β, A, C)` at the point
`(φ_π, φ_x) = (φ₀, 4y₀)`. -/
noncomputable def pReg (β σ κ φ0 y0 : ℝ) : Fin 3 → ℝ :=
  ![1 - β + σ * y0 + σ * κ * φ0, κ * φ0 - κ + (1 - β) * y0,
    2 * (1 + β) + σ * κ * (1 + φ0) + (1 + β) * σ * y0]

/-- Woodford (2003), fn. 33 and App. C.2: the slopes of `(Δ − β, A, C)` along the direction
`(dφ, 4dy)`. -/
noncomputable def qReg (β σ κ dφ dy : ℝ) : Fin 3 → ℝ :=
  ![σ * dy + σ * κ * dφ, κ * dφ + (1 - β) * dy, σ * κ * dφ + (1 + β) * σ * dy]

/-- Woodford (2003), fn. 33: the constant terms of `(−β − Δ, −A, −C)`. -/
noncomputable def pReg' (β σ κ φ0 y0 : ℝ) : Fin 3 → ℝ :=
  ![-(1 + β) - σ * y0 - σ * κ * φ0, -(κ * φ0 - κ + (1 - β) * y0),
    -(2 * (1 + β) + σ * κ * (1 + φ0) + (1 + β) * σ * y0)]

/-- Woodford (2003), fn. 33: the slopes of `(−β − Δ, −A, −C)`. -/
noncomputable def qReg' (β σ κ dφ dy : ℝ) : Fin 3 → ℝ := -qReg β σ κ dφ dy

/-- Woodford (2003), fn. 33, p. 515: along the line `(φ_π, φ_x) = (φ₀ + s dφ, 4(y₀ + s dy))` the
determinacy region is the union of two systems of three affine inequalities in `s`. -/
theorem region_line_iff (β σ κ φ0 y0 dφ dy s : ℝ) :
    TaylorRegion β σ κ (φ0 + s * dφ) (4 * (y0 + s * dy)) ↔
      (∀ i, 0 < pReg β σ κ φ0 y0 i + qReg β σ κ dφ dy i * s) ∨
        (∀ i, 0 < pReg' β σ κ φ0 y0 i + qReg' β σ κ dφ dy i * s) := by
  simp only [TaylorRegion, Fin.forall_fin_succ, IsEmpty.forall_iff,
    pReg, qReg, pReg', qReg', taylorDelta, regA, regC, Pi.neg_apply, Matrix.cons_val_zero,
    Matrix.cons_val_succ, and_true]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · left; exact ⟨by linarith, by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · left; exact ⟨by linarith, by linarith, by linarith⟩
    · right; exact ⟨by linarith, by linarith, by linarith⟩

/-- Woodford (2003), fn. 33, p. 515: the line meets the determinacy region iff one of the two
Fourier–Motzkin conditions holds. -/
theorem exists_region_line_iff (β σ κ φ0 y0 dφ dy : ℝ) :
    (∃ s, TaylorRegion β σ κ (φ0 + s * dφ) (4 * (y0 + s * dy))) ↔
      FM (pReg β σ κ φ0 y0) (qReg β σ κ dφ dy) ∨ FM (pReg' β σ κ φ0 y0) (qReg' β σ κ dφ dy) := by
  simp only [region_line_iff, FM]
  rw [← fm1_iff, ← fm1_iff]
  constructor
  · rintro ⟨s, h | h⟩
    · exact Or.inl ⟨s, h⟩
    · exact Or.inr ⟨s, h⟩
  · rintro (⟨s, h⟩ | ⟨s, h⟩)
    · exact ⟨s, Or.inl h⟩
    · exact ⟨s, Or.inr h⟩

/-! ### Implementability at every `(ρ_r, ρ_u)` -/

/-- Woodford (2003), App. F.4, p. 713: the response i_r of the interest rate to the natural rate
in the ONI plan is positive, `i_r = (λₓ(1 − βρ_r)² + κ²)/h_r > 0` (`κ > 0`, `λₓ, λᵢ ≥ 0`). -/
theorem iRF4_pos {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hlx : 0 ≤ lx) (hli : 0 ≤ li) :
    0 < Noninertial.iRF4 β κ σ lx li ρ := by
  have hh := Noninertial.hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli
  unfold Noninertial.iRF4 Noninertial.xiF4
  have : 0 < lx * (1 - β * ρ) * (1 - β * ρ) + κ ^ 2 := by
    have := mul_nonneg hlx (mul_self_nonneg (1 - β * ρ))
    nlinarith [sq_pos_of_pos hκ]
  positivity

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- **Woodford (2003), Proposition 7.12 for coefficients of any sign, at EVERY `(ρ_r, ρ_u)`**
(pp. 514–515, fn. 33): with AR(1) disturbances non-degenerate as a pair, the optimal
noninertial plan is an equilibrium of some Taylor rule (3.1) (any intercepts, any real
coefficients) implying a determinate equilibrium iff some `(φ_π, φ_x)` solves the consistency
system `i_u = φ_ππ_u + (φ_x/4)x_u`, `i_r = φ_ππ_r + (φ_x/4)x_r` and lies in `TaylorRegion`. -/
theorem oni_implementable_iff_exists [Nonempty Ω] {β κ σ rbar lx li istar ρr ρu : ℝ}
    (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li) {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r) (hnd : Nondeg2 u r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (∃ ibar φπ φx πbar xbar : ℝ, ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) ∧
      TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)) ↔
      ∃ φπ φx : ℝ, Noninertial.iUF4 β κ σ lx li ρu = φπ * Noninertial.piUF4 β κ σ lx li ρu +
          φx / 4 * Noninertial.xUF4 β κ σ lx li ρu ∧
        Noninertial.iRF4 β κ σ lx li ρr = φπ * Noninertial.piRF4 β κ σ lx li ρr +
          φx / 4 * Noninertial.xRF4 β κ σ lx li ρr ∧ TaylorRegion β σ κ φπ φx := by
  set πs := Noninertial.piBar119 β li rbar istar
  obtain ⟨c1, c2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρu) hκ hσ hlx hli
  obtain ⟨c3, c4⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρr) hκ hσ hlx hli
  have hxb : κ * xs = (1 - β) * πs := by rw [hxs]; field_simp
  have hO := plan2_of 𝔼 (rbar := rbar) (πbar := πs) (xbar := xs) hu hr (by linarith [hxb]) his
    c1 c2 c3 c4
  constructor
  · rintro ⟨ibar, φπ, φx, πbar, xbar, hdet, heq⟩
    have hreg := (taylor_determinate_iff_region_any 𝔼 hβ0 hσ).mp hdet
    have hI1 := (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mp heq.2
    have hI2 := (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mp hO.2
    have hi : ∀ t ω, taylorRule ibar φπ φx πbar xbar
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) t ω =
        plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r t ω := by
      intro t ω
      have h := (hI1 t ω).symm.trans (hI2 t ω)
      have : σ * (taylorRule ibar φπ φx πbar xbar
          (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) t ω -
          plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r t ω)
          = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hσ.ne')
    rw [taylorRule_plan2] at hi
    obtain ⟨-, k1, k2⟩ := Noninertial.affine_zero2 hnd
      (a := ibar + φπ * (πs - πbar) + φx * (xs - xbar) / 4 - is)
      (b := φπ * Noninertial.piUF4 β κ σ lx li ρu + φx * Noninertial.xUF4 β κ σ lx li ρu / 4 -
        Noninertial.iUF4 β κ σ lx li ρu)
      (c := φπ * Noninertial.piRF4 β κ σ lx li ρr + φx * Noninertial.xRF4 β κ σ lx li ρr / 4 -
        Noninertial.iRF4 β κ σ lx li ρr) (fun t ω => by
          have h := hi t ω
          simp only [plan2_apply] at h
          linear_combination h)
    exact ⟨φπ, φx, by linear_combination -k1, by linear_combination -k2, hreg⟩
  · rintro ⟨φπ, φx, hU, hR, hreg⟩
    have hrule : plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r =
        taylorRule is φπ φx πs xs
          (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
      rw [taylorRule_plan2, hU, hR]
      congr 1 <;> ring
    have heq : TaylorEqm 𝔼 β σ κ is φπ φx πs xs u (fun t ω => rbar + r t ω)
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
      unfold TaylorEqm
      rw [← hrule]
      exact hO
    exact ⟨is, φπ, φx, πs, xs, (taylor_determinate_iff_region 𝔼 hβ0 hσ hxb).mpr hreg, heq⟩

/-! ### The rank-deficient case -/

/-- **Woodford (2003), Proposition 7.12 at the singular `(ρ_r, ρ_u)` (pp. 514–515, fn. 33), exact,
both directions.** Where the consistency system is singular (`det G = 0`), write
`(a, b, c) = (π_r, x_r, i_r)` (the `rⁿ`-row) and parametrise the line `aφ_π + b(φ_x/4) = c` by
`φ_π = ca/(a² + b²) − sb`, `φ_x/4 = cb/(a² + b²) + sa`. The optimal noninertial plan is the
equilibrium of some determinate Taylor rule (any sign) iff (i) the `rⁿ`-row is nonzero, (ii) the
augmented system has rank one, `π_u i_r = i_u π_r` and `x_u i_r = i_u x_r`, and (iii) one of the
two Fourier–Motzkin conditions (`FM`) for `(Δ − β, A, C)` or `(−β − Δ, −A, −C)` along the line
holds. -/
theorem oni_implementable_singular_iff [Nonempty Ω] {β κ σ rbar lx li istar ρr ρu : ℝ}
    (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li)
    (hd : detG β κ σ lx li (ρr, ρu) = 0) {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r) (hnd : Nondeg2 u r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (∃ ibar φπ φx πbar xbar : ℝ, ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) ∧
      TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)) ↔
      (Noninertial.piRF4 β κ σ lx li ρr ≠ 0 ∨ Noninertial.xRF4 β κ σ lx li ρr ≠ 0) ∧
      Noninertial.piUF4 β κ σ lx li ρu * Noninertial.iRF4 β κ σ lx li ρr =
        Noninertial.iUF4 β κ σ lx li ρu * Noninertial.piRF4 β κ σ lx li ρr ∧
      Noninertial.xUF4 β κ σ lx li ρu * Noninertial.iRF4 β κ σ lx li ρr =
        Noninertial.iUF4 β κ σ lx li ρu * Noninertial.xRF4 β κ σ lx li ρr ∧
      (FM (pReg β σ κ
          (Noninertial.iRF4 β κ σ lx li ρr * Noninertial.piRF4 β κ σ lx li ρr /
            (Noninertial.piRF4 β κ σ lx li ρr ^ 2 + Noninertial.xRF4 β κ σ lx li ρr ^ 2))
          (Noninertial.iRF4 β κ σ lx li ρr * Noninertial.xRF4 β κ σ lx li ρr /
            (Noninertial.piRF4 β κ σ lx li ρr ^ 2 + Noninertial.xRF4 β κ σ lx li ρr ^ 2)))
        (qReg β σ κ (-Noninertial.xRF4 β κ σ lx li ρr) (Noninertial.piRF4 β κ σ lx li ρr)) ∨
       FM (pReg' β σ κ
          (Noninertial.iRF4 β κ σ lx li ρr * Noninertial.piRF4 β κ σ lx li ρr /
            (Noninertial.piRF4 β κ σ lx li ρr ^ 2 + Noninertial.xRF4 β κ σ lx li ρr ^ 2))
          (Noninertial.iRF4 β κ σ lx li ρr * Noninertial.xRF4 β κ σ lx li ρr /
            (Noninertial.piRF4 β κ σ lx li ρr ^ 2 + Noninertial.xRF4 β κ σ lx li ρr ^ 2)))
        (qReg' β σ κ (-Noninertial.xRF4 β κ σ lx li ρr) (Noninertial.piRF4 β κ σ lx li ρr))) := by
  rw [oni_implementable_iff_exists 𝔼 hβ0 hκ hσ hlx hli hu hr hnd hxs his]
  set a := Noninertial.piRF4 β κ σ lx li ρr with ha
  set b := Noninertial.xRF4 β κ σ lx li ρr with hb
  set c := Noninertial.iRF4 β κ σ lx li ρr with hc
  set pu := Noninertial.piUF4 β κ σ lx li ρu with hpu
  set xu := Noninertial.xUF4 β κ σ lx li ρu with hxu
  set iu := Noninertial.iUF4 β κ σ lx li ρu with hiu
  have hcpos : 0 < c := iRF4_pos hκ hlx hli
  have hdet : pu * b - xu * a = 0 := hd
  rw [← exists_region_line_iff]
  constructor
  · rintro ⟨φπ, φx, hU, hR, hreg⟩
    have hrow : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hcon
      push Not at hcon
      rw [hcon.1, hcon.2] at hR
      linarith
    have hn : a ^ 2 + b ^ 2 ≠ 0 := by
      rcases hrow with h | h <;> positivity
    refine ⟨hrow, by linear_combination pu * hR - a * hU + φx / 4 * hdet,
      by linear_combination xu * hR - b * hU - φπ * hdet, ?_⟩
    refine ⟨(-b * φπ + a * (φx / 4)) / (a ^ 2 + b ^ 2), ?_⟩
    have e1 : c * a / (a ^ 2 + b ^ 2) + (-b * φπ + a * (φx / 4)) / (a ^ 2 + b ^ 2) * -b = φπ := by
      field_simp
      linear_combination 4 * a * hR
    have e2 : 4 * (c * b / (a ^ 2 + b ^ 2) + (-b * φπ + a * (φx / 4)) / (a ^ 2 + b ^ 2) * a) =
        φx := by
      field_simp
      linear_combination 4 * b * hR
    rw [e1, e2]
    exact hreg
  · rintro ⟨hrow, hk1, hk2, s, hreg⟩
    have hn : a ^ 2 + b ^ 2 ≠ 0 := by
      rcases hrow with h | h <;> positivity
    set φπ := c * a / (a ^ 2 + b ^ 2) + s * -b with hφ
    set y := c * b / (a ^ 2 + b ^ 2) + s * a with hy
    have hR : c = φπ * a + 4 * y / 4 * b := by
      rw [hφ, hy]
      field_simp
      ring
    have hR' : c = φπ * a + y * b := by rw [hR]; ring
    have hU : iu = φπ * pu + 4 * y / 4 * xu := by
      have h1 : a * (φπ * pu + y * xu - iu) = 0 := by
        linear_combination (-pu) * hR' + hk1 - y * hdet
      have h2 : b * (φπ * pu + y * xu - iu) = 0 := by
        linear_combination (-xu) * hR' + hk2 + φπ * hdet
      have h3 : φπ * pu + y * xu - iu = 0 := by
        rcases hrow with h | h
        · exact (mul_eq_zero.mp h1).resolve_left h
        · exact (mul_eq_zero.mp h2).resolve_left h
      linear_combination -h3
    exact ⟨φπ, 4 * y, hU, hR, hreg⟩

/-- Woodford (2003), App. F.4, p. 713: if `λᵢ(γ_r − ρ_rκσ) = 0` then the ONI plan does not respond
to the natural rate at all, `π_r = x_r = 0` (the `rⁿ`-row of the consistency system vanishes). -/
theorem r_row_zero {β κ σ lx li ρ : ℝ} (h : li * (Noninertial.gamF4 β ρ - ρ * κ * σ) = 0) :
    Noninertial.piRF4 β κ σ lx li ρ = 0 ∧ Noninertial.xRF4 β κ σ lx li ρ = 0 := by
  unfold Noninertial.piRF4 Noninertial.xRF4
  constructor
  · rw [mul_right_comm li σ⁻¹, h, zero_mul, zero_mul, zero_div]
  · rw [mul_right_comm li σ⁻¹, h, zero_mul, zero_mul, zero_div]

/-- **Woodford (2003), Proposition 7.12 when the consistency system has a zero `rⁿ`-row**: if
`λᵢ(γ_r − ρ_rκσ) = 0` — in particular for `λᵢ = 0`, where the system is singular at every
`(ρ_r, ρ_u)` (`TidyR5TaylorRegion.detG_li_zero`) — the optimal noninertial plan is NOT the
equilibrium of any Taylor rule (3.1), determinate or not, of any sign: the interest rate must
respond to `rⁿ` (`iRF4_pos`) while inflation and the gap do not. -/
theorem not_implementable_r_row_zero [Nonempty Ω] {β κ σ rbar lx li istar ρr ρu : ℝ}
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li)
    (h0 : li * (Noninertial.gamF4 β ρr - ρr * κ * σ) = 0) {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r) (hnd : Nondeg2 u r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    ¬ ∃ ibar φπ φx πbar xbar : ℝ,
      TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
  rintro ⟨ibar, φπ, φx, πbar, xbar, heq⟩
  set πs := Noninertial.piBar119 β li rbar istar
  obtain ⟨c1, c2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρu) hκ hσ hlx hli
  obtain ⟨c3, c4⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρr) hκ hσ hlx hli
  have hxb : κ * xs = (1 - β) * πs := by rw [hxs]; field_simp
  have hO := plan2_of 𝔼 (rbar := rbar) (πbar := πs) (xbar := xs) hu hr (by linarith [hxb]) his
    c1 c2 c3 c4
  have hI1 := (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mp heq.2
  have hI2 := (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mp hO.2
  have hi : ∀ t ω, taylorRule ibar φπ φx πbar xbar
      (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
      (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) t ω =
      plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r t ω := by
    intro t ω
    have h := (hI1 t ω).symm.trans (hI2 t ω)
    have : σ * (taylorRule ibar φπ φx πbar xbar
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) t ω -
        plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r t ω)
        = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hσ.ne')
  rw [taylorRule_plan2] at hi
  obtain ⟨-, -, k2⟩ := Noninertial.affine_zero2 hnd
    (a := ibar + φπ * (πs - πbar) + φx * (xs - xbar) / 4 - is)
    (b := φπ * Noninertial.piUF4 β κ σ lx li ρu + φx * Noninertial.xUF4 β κ σ lx li ρu / 4 -
      Noninertial.iUF4 β κ σ lx li ρu)
    (c := φπ * Noninertial.piRF4 β κ σ lx li ρr + φx * Noninertial.xRF4 β κ σ lx li ρr / 4 -
      Noninertial.iRF4 β κ σ lx li ρr) (fun t ω => by
        have h := hi t ω
        simp only [plan2_apply] at h
        linear_combination h)
  obtain ⟨z1, z2⟩ := r_row_zero (lx := lx) h0
  rw [z1, z2] at k2
  have := iRF4_pos (β := β) (σ := σ) (ρ := ρr) hκ hlx hli
  linarith

/-- **Woodford (2003), p. 515, with `λᵢ = 0`**: the consistency system is singular everywhere and
the optimal noninertial plan is never the equilibrium of a Taylor rule (3.1), at any
`(ρ_r, ρ_u)`, with coefficients of any sign. -/
theorem not_implementable_li_zero [Nonempty Ω] {β κ σ rbar lx istar ρr ρu : ℝ} (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 ≤ lx) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r)
    (hnd : Nondeg2 u r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β 0 rbar istar)
    (his : is = rbar + Noninertial.piBar119 β 0 rbar istar) :
    ¬ ∃ ibar φπ φx πbar xbar : ℝ,
      TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 β 0 rbar istar) (Noninertial.piUF4 β κ σ lx 0 ρu)
          (Noninertial.piRF4 β κ σ lx 0 ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx 0 ρu) (Noninertial.xRF4 β κ σ lx 0 ρr) u r) :=
  not_implementable_r_row_zero 𝔼 hκ hσ hlx le_rfl (by ring) hu hr hnd hxs his

end Woodford.GainsFromCommitment.TidyR6TaylorSingular
