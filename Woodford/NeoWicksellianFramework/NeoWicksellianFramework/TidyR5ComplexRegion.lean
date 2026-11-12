/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Prop410Complex

/-!
# Proposition 4.10 for complex eigenvalues of `C`: the exact E-stability region

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, Proposition 4.10, pp. 274–275 (Preston
(2005), App. 4). Proposition 4.10 assumes the eigenvalues of `C` real; the module Prop410Complex
shows the assumption cannot be dropped. Here the E-stability region is characterised
**exactly** for an arbitrary stationary `C` (complex eigenvalues allowed, no diagonalisability),
with both directions proved.

* `roots_of_hurwitz`, **`hurwitz_iff`**: both roots of `ν² + c₁ν + c₀` (complex coefficients)
  have negative real part **iff** `Re c₁ > 0` and
  `(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)² > 0` (the complex Routh–Hurwitz criterion for
  quadratics; `Prop410Complex.hurwitz_of_roots` was the necessity half);
  `eig_re_lt_one_iff_hurwitz`: a complex `2 × 2` matrix `R` has every eigenvalue with real part
  `< 1` iff `HurwitzC R`.
* `gC`, `bTilC`: `G(ρ) = ρ/(1 − αβρ) A₁ + ρ/(1 − βρ) A₂` and its restriction `B̃(ρ)` to the
  Taylor-rule plane for complex `ρ`; `nPolyC`, `trPolyC`, `bTilC_det_identity`,
  `bTilC_tr_identity`: `Δ(1 − αβρ)(1 − βρ)` times the Hurwitz coefficients
  `c₀ = 1 − tr B̃ + det B̃`, `c₁ = 2 − tr B̃` are the polynomials of the real case evaluated at
  complex `ρ`; `hurwitzC_bTilC_iff`: the condition in closed form.
* **`eStable_hMat_iff`**: `H` is E-stable iff `HurwitzC(B̃(ρ))` for **every** eigenvalue `ρ` of
  `C` (both directions: `Prop410.isEig_hMat_sub` and `Prop410Complex.isEig_hMat_of`).
* `hurwitzC_of_real`: for any real `r ≤ 1` the condition follows from (2.7).
* **`prop_4_10_complex`**: for any stationary `C`, a fixed point of Preston's `T`-map is E-stable
  iff the Taylor principle (2.7) holds **and** `HurwitzC(B̃(ρ))` holds at every non-real
  eigenvalue `ρ` of `C`; `prop_4_10_complex_explicit`: the same with the closed forms.
* `cexC2`, `prop_4_10_complex_stable_case`: the extra condition is not always violated: with
  the parameters of the module Prop410Complex and `C` a rotation with eigenvalues `±i/2`, the
  r.e.e. exists, is unique and is E-stable. Together with
  `Prop410Complex.prop_4_10_needs_real_eigenvalues`, for complex `C` E-stability depends on `C`
  and not only on (2.7).
-/

namespace Woodford.NeoWicksellianFramework.TidyR5ComplexRegion

open Matrix Determinacy2 PrestonLearning Prop410 Prop410Complex
open Determinacy2Learning (EStable EStableAt eStable_iff)
open scoped _root_.Kronecker

/-! ### The complex Routh–Hurwitz criterion for quadratics -/

/-- Woodford (2003), p. 274 (E-stability for complex blocks; sufficiency of the complex
Hurwitz condition): if `Re c₁ > 0` and `(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)² > 0`, every
root of `ν² + c₁ν + c₀` has negative real part. With roots `xᵢ + i yᵢ` the second expression is
`x₁x₂((x₁ + x₂)² + (y₁ − y₂)²)` and `Re c₁ = −(x₁ + x₂)`. -/
theorem roots_of_hurwitz (c1 c0 : ℂ) (h1 : 0 < c1.re)
    (h2 : 0 < c1.re ^ 2 * c0.re + c1.re * c1.im * c0.im - c0.im ^ 2) (ν : ℂ)
    (hν : ν ^ 2 + c1 * ν + c0 = 0) : ν.re < 0 := by
  have hc1 : c1 = -(ν + (-c1 - ν)) := by ring
  have hc0 : c0 = ν * (-c1 - ν) := by linear_combination hν
  set ν2 := -c1 - ν with hν2
  rw [hc1, hc0] at h2
  rw [hc1] at h1
  simp only [Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im] at h1 h2
  have key : (-(ν.re + ν2.re)) ^ 2 * (ν.re * ν2.re - ν.im * ν2.im) +
      -(ν.re + ν2.re) * -(ν.im + ν2.im) * (ν.re * ν2.im + ν.im * ν2.re) -
      (ν.re * ν2.im + ν.im * ν2.re) ^ 2 =
      ν.re * ν2.re * ((ν.re + ν2.re) ^ 2 + (ν.im - ν2.im) ^ 2) := by ring
  rw [key] at h2
  have hP : 0 < (ν.re + ν2.re) ^ 2 + (ν.im - ν2.im) ^ 2 := by
    have : 0 < (ν.re + ν2.re) ^ 2 := by
      have : ν.re + ν2.re < 0 := by linarith
      nlinarith
    nlinarith [sq_nonneg (ν.im - ν2.im)]
  have hx : 0 < ν.re * ν2.re := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith

/-- Woodford (2003), p. 274: **the complex Routh–Hurwitz criterion for quadratics**: both roots
of `ν² + c₁ν + c₀` have negative real part iff `Re c₁ > 0` and
`(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)² > 0`. -/
theorem hurwitz_iff (c1 c0 : ℂ) :
    (∀ ν : ℂ, ν ^ 2 + c1 * ν + c0 = 0 → ν.re < 0) ↔
      (0 < c1.re ∧ 0 < c1.re ^ 2 * c0.re + c1.re * c1.im * c0.im - c0.im ^ 2) :=
  ⟨hurwitz_of_roots c1 c0, fun h => roots_of_hurwitz c1 c0 h.1 h.2⟩

/-- Woodford (2003), p. 274: the E-stability condition for a complex `2 × 2` block `R`
(`R − I` Hurwitz): `Re(2 − tr R) > 0` and `hurwitzVal R > 0`. -/
def HurwitzC (R : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  0 < (2 - (R 0 0 + R 1 1)).re ∧ 0 < hurwitzVal R

/-- Woodford (2003), p. 274: **every eigenvalue of a complex `2 × 2` matrix `R` has real part
`< 1` iff `HurwitzC R`**. -/
theorem eig_re_lt_one_iff_hurwitz (R : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ μ, KroneckerSpectrum.IsEig R μ → μ.re < 1) ↔ HurwitzC R := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨μ, hμ, hμ1⟩ := exists_isEig_re_ge_one R hc
    have := h μ hμ
    linarith
  · intro h μ hμ
    have hq := (isEig_two_iff_complex R μ).mp hμ
    have := roots_of_hurwitz _ _ h.1 h.2 (μ - 1) (by linear_combination hq)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith

/-! ### The blocks `G(ρ)` and `B̃(ρ)` for complex `ρ` -/

/-- Woodford (2003), p. 275 (Preston (2005), App. 4): `G(ρ) = ρ/(1 − αβρ) A₁ + ρ/(1 − βρ) A₂`
for a complex eigenvalue `ρ` of `C`. -/
noncomputable def gC (α β κ σ φπ φx : ℝ) (ρ : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (ρ / (1 - ((α * β : ℝ) : ℂ) * ρ)) • (matS α β κ σ φπ φx).map Complex.ofReal +
    (ρ / (1 - (β : ℂ) * ρ)) • (matD β κ σ φπ φx).map Complex.ofReal

/-- Woodford (2003), p. 275: `B̃(ρ)`, the restriction of `G(ρ)` to the Taylor-rule plane
`î = φ_π π + φ_x x/4`, for complex `ρ`. -/
noncomputable def bTilC (α β κ σ φπ φx : ℝ) (ρ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  restr (gC α β κ σ φπ φx ρ) (φπ : ℂ) ((φx / 4 : ℝ) : ℂ)

/-- Woodford (2003), p. 275: the eigenvalues of `G(ρ)` are `0` and those of `B̃(ρ)`. -/
theorem isEig_gC_iff (α β κ σ φπ φx : ℝ) (ρ μ : ℂ) :
    KroneckerSpectrum.IsEig (gC α β κ σ φπ φx ρ) μ ↔
      μ = 0 ∨ KroneckerSpectrum.IsEig (bTilC α β κ σ φπ φx ρ) μ :=
  isEig_three_iff _ _ _ (row_two_complex α β κ σ φπ φx _ _) μ

/-- Woodford (2003), p. 275: `nPoly` at a complex `ρ`:
`1 − (1 + β + κσ)ρ + βρ² + σκφ_π + (1 − βρ)σφ_x/4`. -/
noncomputable def nPolyC (β κ σ φπ φx : ℝ) (r : ℂ) : ℂ :=
  1 - (1 + β + κ * σ) * r + β * r ^ 2 + σ * κ * φπ + (1 - β * r) * (σ * φx / 4)

/-- Woodford (2003), p. 275: `trPoly` at a complex `ρ`. -/
noncomputable def trPolyC (α β κ σ φπ φx : ℝ) (r : ℂ) : ℂ :=
  2 * (1 - α * β * r) * (1 - β * r) - (1 - α) * β * r * (1 - β * r) -
    (κ * σ + 1 - β) * r * (1 - α * β * r) + σ * κ * ((1 - α * β * r) + (1 - β * r)) * φπ +
    ((1 - α * β * r) * (1 - β * r) + (1 - β * r) + (1 - α) * β ^ 2 * r ^ 2) * (σ * φx / 4)

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, the coefficient `c` at complex `ρ`):
`Δ(1 − αβρ)(1 − βρ)(1 − tr B̃(ρ) + det B̃(ρ)) = nPoly(ρ)`. -/
theorem bTilC_det_identity {α β κ σ φπ φx : ℝ} {r : ℂ} (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hP : 1 - ((α * β : ℝ) : ℂ) * r ≠ 0) (hQ : 1 - (β : ℂ) * r ≠ 0) :
    (taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * r) * (1 - (β : ℂ) * r) *
        (1 - (bTilC α β κ σ φπ φx r 0 0 + bTilC α β κ σ φπ φx r 1 1) +
          (bTilC α β κ σ φπ φx r 0 0 * bTilC α β κ σ φπ φx r 1 1 -
            bTilC α β κ σ φπ φx r 0 1 * bTilC α β κ σ φπ φx r 1 0)) =
      nPolyC β κ σ φπ φx r := by
  have hΔe : (taylorDelta σ κ φπ φx : ℂ) = 1 + σ * φx / 4 + σ * κ * φπ := by
    simp [taylorDelta]
  have hΔc : (taylorDelta σ κ φπ φx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔ
  simp only [bTilC, gC, restr, matS, matD, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    vecMulVec_apply, smul_eq_mul, colS, colD, supplyW, demandW, nPolyC, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  push_cast at hP ⊢
  field_simp
  rw [hΔe]
  ring

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, the coefficient `b` at complex `ρ`):
`Δ(1 − αβρ)(1 − βρ)(2 − tr B̃(ρ)) = trPoly(ρ)`. -/
theorem bTilC_tr_identity {α β κ σ φπ φx : ℝ} {r : ℂ} (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hP : 1 - ((α * β : ℝ) : ℂ) * r ≠ 0) (hQ : 1 - (β : ℂ) * r ≠ 0) :
    (taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * r) * (1 - (β : ℂ) * r) *
        (2 - (bTilC α β κ σ φπ φx r 0 0 + bTilC α β κ σ φπ φx r 1 1)) =
      trPolyC α β κ σ φπ φx r := by
  have hΔe : (taylorDelta σ κ φπ φx : ℂ) = 1 + σ * φx / 4 + σ * κ * φπ := by
    simp [taylorDelta]
  have hΔc : (taylorDelta σ κ φπ φx : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔ
  simp only [bTilC, gC, restr, matS, matD, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    vecMulVec_apply, smul_eq_mul, colS, colD, supplyW, demandW, trPolyC, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  push_cast at hP ⊢
  field_simp
  rw [hΔe]
  ring

/-- Woodford (2003), p. 275: the Hurwitz expression `(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ −
(Im c₀)²` of a pair of complex coefficients. -/
noncomputable def hurwitzExpr (c1 c0 : ℂ) : ℝ :=
  c1.re ^ 2 * c0.re + c1.re * c1.im * c0.im - c0.im ^ 2

/-- Woodford (2003), p. 275: **the E-stability condition of the block `ρ` in closed form**: with
`D(ρ) = Δ(1 − αβρ)(1 − βρ)`, `c₁ = trPoly(ρ)/D(ρ)` and `c₀ = nPoly(ρ)/D(ρ)`, `HurwitzC(B̃(ρ))`
iff `Re c₁ > 0` and `(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)² > 0`. -/
theorem hurwitzC_bTilC_iff {α β κ σ φπ φx : ℝ} {r : ℂ} (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (hP : 1 - ((α * β : ℝ) : ℂ) * r ≠ 0) (hQ : 1 - (β : ℂ) * r ≠ 0) :
    HurwitzC (bTilC α β κ σ φπ φx r) ↔
      (0 < (trPolyC α β κ σ φπ φx r /
          ((taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * r) * (1 - (β : ℂ) * r))).re ∧
        0 < hurwitzExpr (trPolyC α β κ σ φπ φx r /
            ((taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * r) * (1 - (β : ℂ) * r)))
          (nPolyC β κ σ φπ φx r /
            ((taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * r) * (1 - (β : ℂ) * r)))) := by
  have hD : (taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * r) * (1 - (β : ℂ) * r) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hΔ) hP) hQ
  have e1 := bTilC_tr_identity hΔ hP hQ (κ := κ)
  have e0 := bTilC_det_identity hΔ hP hQ (κ := κ)
  rw [← e1, ← e0, mul_div_cancel_left₀ _ hD, mul_div_cancel_left₀ _ hD]
  rfl

/-! ### The exact E-stability region of `H` -/

/-- Woodford (2003), p. 275 (Preston (2005), App. 4, without diagonalisability): **for a
stationary real `C`, `H = ((I − αβC)⁻¹C)′ ⊗ A₁ + ((I − βC)⁻¹C)′ ⊗ A₂` is E-stable iff
`HurwitzC(B̃(ρ))` holds at every (complex) eigenvalue `ρ` of `C`.** -/
theorem eStable_hMat_iff {n : ℕ} {α β κ σ φπ φx : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1) :
    EStable (hMat α β κ σ φπ φx C) ↔
      ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ →
        HurwitzC (bTilC α β κ σ φπ φx ρ) := by
  rw [eStable_iff]
  constructor
  · intro h ρ hρ
    rw [← eig_re_lt_one_iff_hurwitz]
    intro μ hμ
    have hρT : KroneckerSpectrum.IsEig (C.map Complex.ofReal)ᵀ ρ :=
      (KroneckerSpectrum.isEig_transpose_iff _ ρ).mpr hρ
    obtain ⟨w, hw0, hw⟩ := hρT
    rw [Matrix.mulVec_transpose] at hw
    have hG : KroneckerSpectrum.IsEig (gC α β κ σ φπ φx ρ) μ :=
      (isEig_gC_iff α β κ σ φπ φx ρ μ).mpr (Or.inr hμ)
    exact h μ (isEig_hMat_of hα0 hα1 hβ0 hβ1 hC (hC ρ hρ) hw0 hw hG)
  · intro h μ hμ
    obtain ⟨ρ, hρ, hG⟩ := isEig_hMat_sub hα0 hα1 hβ0 hβ1 hC hμ
    rcases (isEig_gC_iff α β κ σ φπ φx ρ μ).mp hG with h0 | h2
    · rw [h0]
      norm_num
    · exact (eig_re_lt_one_iff_hurwitz _).mpr (h ρ hρ) μ h2

/-- Woodford (2003), p. 275: under the Taylor principle (2.7) the condition holds at every real
`ρ ≤ 1` (the real case of Proposition 4.10, `Prop410.eStable_gMat_of_taylor`). -/
theorem hurwitzC_of_real {α β κ σ φπ φx r : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ) (hx : 0 ≤ φx)
    (hT : 1 < taylorLHS β κ φπ φx) (hr : r ≤ 1) : HurwitzC (bTilC α β κ σ φπ φx (r : ℂ)) := by
  rw [← eig_re_lt_one_iff_hurwitz]
  intro μ hμ
  have hE := eStable_gMat_of_taylor hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hT hr
  have hG : KroneckerSpectrum.IsEig (gC α β κ σ φπ φx (r : ℂ)) μ :=
    (isEig_gC_iff α β κ σ φπ φx _ μ).mpr (Or.inr hμ)
  rw [gC, ← gMat_map] at hG
  exact (eStable_iff _).mp hE μ hG

/-- Woodford (2003), **Proposition 4.10 for an arbitrary stationary `C`** (complex eigenvalues
allowed, no diagonalisability): with `0 < β < 1`, `0 ≤ α < 1`, `κ, σ > 0`, `φ_π, φ_x ≥ 0` and
every eigenvalue of `C` inside the unit circle, a fixed point of Preston's `T`-map is E-stable
**iff** the Taylor principle (2.7) holds **and** `HurwitzC(B̃(ρ))` holds at every non-real
eigenvalue `ρ` of `C`. For real `C`-eigenvalues the extra condition is vacuous (the book's
Proposition 4.10); `Prop410Complex.prop_4_10_needs_real_eigenvalues` and
`prop_4_10_complex_stable_case` show it can fail and can hold. -/
theorem prop_4_10_complex {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hπ : 0 ≤ φπ)
    (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    EStableAt (tVecP α β κ σ φπ φx c gr gi C) v ↔
      1 < taylorLHS β κ φπ φx ∧
        ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im ≠ 0 →
          HurwitzC (bTilC α β κ σ φπ φx ρ) := by
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  rw [eStableAt_tVecP_iff hfix (det_one_sub_smul_ne_zero hC hab) (det_one_sub_smul_ne_zero hC hb),
    eStable_dTP_iff_and, eStable_aInt_iff hα0 hα1 hβ0 hβ1 hκ hσ hπ hx,
    eStable_hMat_iff hα0 hα1 hβ0 hβ1 hC]
  constructor
  · rintro ⟨hT, h⟩
    exact ⟨hT, fun ρ hρ _ => h ρ hρ⟩
  · rintro ⟨hT, h⟩
    refine ⟨hT, fun ρ hρ => ?_⟩
    by_cases him : ρ.im = 0
    · have hρr : ρ = (ρ.re : ℂ) := Complex.ext (by simp) (by simp [him])
      have hr : ρ.re ≤ 1 := (abs_le.mp ((Complex.abs_re_le_norm ρ).trans (hC ρ hρ).le)).2
      rw [hρr]
      exact hurwitzC_of_real hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hT hr
    · exact h ρ hρ him

/-- Woodford (2003), Proposition 4.10 for an arbitrary stationary `C`, **in closed form**: a
fixed point of Preston's `T`-map is E-stable iff (2.7) holds and, at every non-real eigenvalue
`ρ` of `C`, with `D(ρ) = Δ(1 − αβρ)(1 − βρ)`, `c₁ = trPoly(ρ)/D(ρ)`, `c₀ = nPoly(ρ)/D(ρ)`:
`Re c₁ > 0` and `(Re c₁)² Re c₀ + Re c₁ Im c₁ Im c₀ − (Im c₀)² > 0`. -/
theorem prop_4_10_complex_explicit {n : ℕ} {α β κ σ φπ φx c : ℝ} {gr gi : Fin n → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hπ : 0 ≤ φπ) (hx : 0 ≤ φx) {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ‖ρ‖ < 1)
    {v : IdxP n → ℝ} (hfix : tVecP α β κ σ φπ φx c gr gi C v = v) :
    EStableAt (tVecP α β κ σ φπ φx c gr gi C) v ↔
      1 < taylorLHS β κ φπ φx ∧
        ∀ ρ, KroneckerSpectrum.IsEig (C.map Complex.ofReal) ρ → ρ.im ≠ 0 →
          (0 < (trPolyC α β κ σ φπ φx ρ /
              ((taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * ρ) *
                (1 - (β : ℂ) * ρ))).re ∧
            0 < hurwitzExpr (trPolyC α β κ σ φπ φx ρ /
                ((taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * ρ) * (1 - (β : ℂ) * ρ)))
              (nPolyC β κ σ φπ φx ρ /
                ((taylorDelta σ κ φπ φx : ℂ) * (1 - ((α * β : ℝ) : ℂ) * ρ) *
                  (1 - (β : ℂ) * ρ)))) := by
  rw [prop_4_10_complex hα0 hα1 hβ0 hβ1 hκ hσ hπ hx hC hfix]
  have hΔ := (taylorDelta_pos hσ hκ hπ hx).ne'
  have hne : ∀ a : ℝ, |a| ≤ 1 → ∀ ρ, ‖ρ‖ < 1 → 1 - (a : ℂ) * ρ ≠ 0 := by
    intro a ha ρ hρ h0
    have h1 : (a : ℂ) * ρ = 1 := by linear_combination -h0
    have h2 := congrArg norm h1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_one] at h2
    nlinarith [norm_nonneg ρ, abs_nonneg a]
  have hab : |α * β| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hb : |β| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  refine and_congr_right fun _ => forall_congr' fun ρ => forall_congr' fun hρ =>
    forall_congr' fun _ => ?_
  exact hurwitzC_bTilC_iff hΔ (hne _ hab ρ (hC ρ hρ)) (hne _ hb ρ (hC ρ hρ))

/-! ### Complex eigenvalues need not destroy E-stability -/

/-- Woodford (2003), (2.24): a stationary state matrix with purely imaginary eigenvalues
`±i/2` (a rotation by a quarter turn, damped by `1/2`). -/
noncomputable def cexC2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, -(1 / 2); 1 / 2, 0]

/-- Woodford (2003), (2.24): the eigenvalues of `cexC2` are `±i/2`. -/
theorem cexC2_eig_cases {μ : ℂ} (h : KroneckerSpectrum.IsEig (cexC2.map Complex.ofReal) μ) :
    μ = 1 / 2 * Complex.I ∨ μ = -(1 / 2 * Complex.I) := by
  rw [isEig_two_iff_complex] at h
  simp only [cexC2, Fin.isValue, map_apply, of_apply, cons_val', cons_val_zero,
    cons_val_fin_one, cons_val_one, Complex.ofReal_zero, Complex.ofReal_neg,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at h
  have : (μ - 1 / 2 * Complex.I) * (μ + 1 / 2 * Complex.I) = 0 := by
    linear_combination h - (1 / 4 : ℂ) * Complex.I_sq
  rcases mul_eq_zero.mp this with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-- Woodford (2003), (2.24): `cexC2` is stationary and has a non-real eigenvalue. -/
theorem cexC2_stationary :
    (∀ ρ, KroneckerSpectrum.IsEig (cexC2.map Complex.ofReal) ρ → ‖ρ‖ < 1) ∧
      KroneckerSpectrum.IsEig (cexC2.map Complex.ofReal) (1 / 2 * Complex.I) := by
  refine ⟨fun ρ hρ => ?_, ?_⟩
  · rcases cexC2_eig_cases hρ with rfl | rfl
    · rw [norm_mul, Complex.norm_I]
      norm_num
    · rw [norm_neg, norm_mul, Complex.norm_I]
      norm_num
  · rw [isEig_two_iff_complex]
    simp only [cexC2, Fin.isValue, map_apply, of_apply, cons_val', cons_val_zero,
      cons_val_fin_one, cons_val_one, Complex.ofReal_zero, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    linear_combination (1 / 4 : ℂ) * Complex.I_sq

/-- Woodford (2003), p. 275: in the example `B̃(±i/2) = p X + q Y` with
`p = ρ/(1 − αβρ) = (−891000 ± 2000000 i)/4793881`, `q = ρ/(1 − βρ) = (−9900 ± 20000 i)/49801`. -/
theorem bTilC_cex2 (s : ℝ) (hs : s = 1 ∨ s = -1) :
    bTilC (9 / 10) (99 / 100) 1 (1 / 100) 8 0 ((s : ℂ) * (1 / 2 * Complex.I)) =
      rCex ⟨-(891000 / 4793881), s * (2000000 / 4793881)⟩
        ⟨-(9900 / 49801), s * (20000 / 49801)⟩ := by
  have hp : (s : ℂ) * (1 / 2 * Complex.I) /
      (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * ((s : ℂ) * (1 / 2 * Complex.I))) =
      ⟨-(891000 / 4793881), s * (2000000 / 4793881)⟩ := by
    have hne : (1 - (((9 / 10 * (99 / 100) : ℝ)) : ℂ) * ((s : ℂ) * (1 / 2 * Complex.I))) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    rw [div_eq_iff hne]
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    apply Complex.ext <;> simp <;> nlinarith [hs2]
  have hq : (s : ℂ) * (1 / 2 * Complex.I) /
      (1 - ((99 / 100 : ℝ) : ℂ) * ((s : ℂ) * (1 / 2 * Complex.I))) =
      ⟨-(9900 / 49801), s * (20000 / 49801)⟩ := by
    have hne : (1 - ((99 / 100 : ℝ) : ℂ) * ((s : ℂ) * (1 / 2 * Complex.I))) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    rw [div_eq_iff hne]
    have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    apply Complex.ext <;> simp <;> nlinarith [hs2]
  rw [bTilC, gC, restr_pq, restrS_cex, restrD_cex, hp, hq]
  rfl

/-- Woodford (2003), p. 275: in the example the block condition holds at both eigenvalues
`±i/2` (`Re c₁ ≈ 1.99`, Hurwitz value `≈ 3.92`). -/
theorem hurwitzC_cex2 (s : ℝ) (hs : s = 1 ∨ s = -1) :
    HurwitzC (bTilC (9 / 10) (99 / 100) 1 (1 / 100) 8 0 ((s : ℂ) * (1 / 2 * Complex.I))) := by
  rw [bTilC_cex2 s hs]
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · simp only [rCex, xCex, yCex, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat]
    norm_num
  · simp only [hurwitzVal, rCex, xCex, yCex, Matrix.add_apply, Matrix.smul_apply,
      Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.re_ofNat, Complex.im_ofNat]
    ring_nf
    rw [hs2]
    norm_num

/-- Woodford (2003), Proposition 4.10 with complex eigenvalues: **complex eigenvalues of `C`
need not destroy E-stability.** With the parameters of the module Prop410Complex
(`α = 0.9`, `β = 0.99`, `κ = 1`, `σ = 0.01`, `φ_π = 8`, `φ_x = 0`, so (2.7) holds) and the
stationary `C = [[0, −1/2], [1/2, 0]]` (eigenvalues `±i/2`), Preston's r.e.e. exists, is unique
and is E-stable, for any Taylor-rule constant and loadings `f_r`, `f_ī`. -/
theorem prop_4_10_complex_stable_case (c : ℝ) (gr gi : Fin 2 → ℝ) :
    1 < taylorLHS (99 / 100) 1 8 0 ∧
      (∃ ρ, KroneckerSpectrum.IsEig (cexC2.map Complex.ofReal) ρ ∧ ρ.im ≠ 0) ∧
      ∃! v, tVecP (9 / 10) (99 / 100) 1 (1 / 100) 8 0 c gr gi cexC2 v = v ∧
        EStableAt (tVecP (9 / 10) (99 / 100) 1 (1 / 100) 8 0 c gr gi cexC2) v := by
  have hT : 1 < taylorLHS (99 / 100) 1 8 0 := by norm_num [taylorLHS]
  have hH : ∀ ρ, KroneckerSpectrum.IsEig (cexC2.map Complex.ofReal) ρ →
      HurwitzC (bTilC (9 / 10) (99 / 100) 1 (1 / 100) 8 0 ρ) := by
    intro ρ hρ
    rcases cexC2_eig_cases hρ with rfl | rfl
    · simpa using hurwitzC_cex2 1 (Or.inl rfl)
    · simpa using hurwitzC_cex2 (-1) (Or.inr rfl)
  have hE : EStable (dTP (9 / 10) (99 / 100) 1 (1 / 100) 8 0 cexC2) := by
    rw [eStable_dTP_iff_and]
    refine ⟨(eStable_aInt_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) le_rfl).mpr hT, ?_⟩
    exact (eStable_hMat_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      cexC2_stationary.1).mpr hH
  have hdet : (1 - dTP (9 / 10) (99 / 100) 1 (1 / 100) 8 0 cexC2).det ≠ 0 :=
    KroneckerSpectrum.det_one_sub_ne_zero _ fun h => by
      have := (eStable_iff _).mp hE 1 h
      norm_num at this
  refine ⟨hT, ⟨_, cexC2_stationary.2, by simp⟩, ?_⟩
  obtain ⟨v, hv, huniq⟩ := fixed_existsUnique_of_det _ _ _ _ _ _ c gr gi cexC2 hdet
  refine ⟨v, ⟨hv, ?_⟩, fun w hw => huniq w hw.1⟩
  have hab : |(9 / 10 : ℝ) * (99 / 100)| ≤ 1 := by norm_num [abs_le]
  have hb : |(99 / 100 : ℝ)| ≤ 1 := by norm_num [abs_le]
  exact (eStableAt_tVecP_iff hv (det_one_sub_smul_ne_zero cexC2_stationary.1 hab)
    (det_one_sub_smul_ne_zero cexC2_stationary.1 hb)).mpr hE

end Woodford.NeoWicksellianFramework.TidyR5ComplexRegion
