/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bGovRamsey
import StabilizationWelfare.TidyR6bRamseyNewton

/-!
# The linearised Ramsey operator with an extra output weight: inverse on event trees

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the commitment system and its root
condition), Chapter 6, §5 (government purchases), and Appendix A.3.

With purchases the linearised output condition has the extra term `γŷ` (`TidyR6bGovRamsey.DQrX`,
`γ = γ_G`). The reduction of `NonlinearNKMarkovRamseyLin` goes through with the targeting rule
`H(ŷ − ŷ₋) + A_uGθπ = ⋯`, `H = A_uG − γ` (`red_targetX`): the commitment system becomes
`ŷ − ŷ₋ + θ_Xπ = f` with `θ_X = A_uGθ/H` (`thX`), and the root condition is that of
`βz² − (1 + β + κθ_X)z + 1`. Under the root condition `TidyR6bGovRamseyTree.RootOK` (`H ≠ 0` and
`κθ_X > 0`, which
holds iff `A_uG·H > 0`, or `κθ_X < −2(1+β)`, an oscillating stable root) there is one root
`|z₁| < 1 < |z₂|` (`z_propsX`), and the inverse of `NonlinearNKMarkovRamseyTree` is rebuilt
with `θ_X`, `H` and the (possibly negative) stable root (restated from that module).

* `thX`, `TidyR6bGovRamseyTree.RootOK`, `z1X`, `z2X`, `thX_props`, `z_propsX`, `abs_inv_z2X`,
  `rootOK_of_pos`,
  `abs_bwd_le'`; `TidyR6bGovRamseyTree.red_l1X`, `red_otherX`, `red_xX`, `red_DX`, `red_muX`,
  `red_pcX`,
  `red_targetX`, `commitment_systemX`.
* `LRX`, `TidyR6bGovRamseyTree.LinvRX`, the uniform bounds `bd_*X`, **`LRX_LinvRX`**, **`LRX_inj`**,
  **`LinvRX_bound`** (the three properties of `TidyR6bRamseyNewton.InvBound`, used in
  `TidyR6bGovRamseyIFT.invBound_gov`).
-/

namespace Woodford.StabilizationWelfare.TidyR6bGovRamseyTree

open Filter Topology
open NonlinearNKMarkov hiding M_lin
open NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree TidyR6bGovRamsey

/-! ## The modified root condition -/

/-- Woodford (2003), Ch. 7: the effective `θ` of the targeting rule, `θ_X = A_uGθ/H`,
`H = A_uG − γ`. -/
noncomputable def thX (p : Par) (R : RPar) (γ : ℝ) : ℝ :=
  R.Au * Gw p R * p.θ / (R.Au * Gw p R - γ)

/-- Woodford (2003), Ch. 7, (1.20) (**the root condition with an extra output weight**): the
output weight is nonzero and `κθ_X > 0` (one root in `(0, 1)`) or `κθ_X < −2(1+β)` (one root in
`(−1, 0)`, oscillating). -/
def RootOK (p : Par) (R : RPar) (γ : ℝ) : Prop :=
  R.Au * Gw p R - γ ≠ 0 ∧ (0 < p.κ * thX p R γ ∨ p.κ * thX p R γ < -(2 * (1 + p.β)))

/-- Woodford (2003), Ch. 7: the stable root of `βz² − (1+β+κθ_X)z + 1` (the root of smaller
modulus). -/
noncomputable def z1X (p : Par) (R : RPar) (γ : ℝ) : ℝ :=
  if 0 ≤ 1 + p.β + p.κ * thX p R γ then
    ((1 + p.β + p.κ * thX p R γ) - Real.sqrt ((1 + p.β + p.κ * thX p R γ) ^ 2 - 4 * p.β)) /
      (2 * p.β)
  else
    ((1 + p.β + p.κ * thX p R γ) + Real.sqrt ((1 + p.β + p.κ * thX p R γ) ^ 2 - 4 * p.β)) /
      (2 * p.β)

/-- Woodford (2003), Ch. 7: the unstable root of `βz² − (1+β+κθ_X)z + 1`. -/
noncomputable def z2X (p : Par) (R : RPar) (γ : ℝ) : ℝ :=
  if 0 ≤ 1 + p.β + p.κ * thX p R γ then
    ((1 + p.β + p.κ * thX p R γ) + Real.sqrt ((1 + p.β + p.κ * thX p R γ) ^ 2 - 4 * p.β)) /
      (2 * p.β)
  else
    ((1 + p.β + p.κ * thX p R γ) - Real.sqrt ((1 + p.β + p.κ * thX p R γ) ^ 2 - 4 * p.β)) /
      (2 * p.β)

/-- Woodford (2003), Ch. 7: under the root condition, `θ_X ≠ 0`, `Hθ_X = A_uGθ`, `H ≠ 0` and
`A_uG ≠ 0`. -/
theorem thX_props {p : Par} (R : RPar) (hp : p.Std) {γ : ℝ} (hpos : RootOK p R γ) :
    thX p R γ ≠ 0 ∧ (R.Au * Gw p R - γ) * thX p R γ = R.Au * Gw p R * p.θ ∧
      R.Au * Gw p R - γ ≠ 0 ∧ R.Au * Gw p R ≠ 0 := by
  obtain ⟨hH, hc⟩ := hpos
  have hθ := lt_trans one_pos hp.one_lt_θ
  have ht : thX p R γ ≠ 0 := fun h => by
    rw [h, mul_zero] at hc
    rcases hc with h1 | h1
    · exact lt_irrefl _ h1
    · linarith [hp.β_pos]
  refine ⟨ht, by unfold thX; field_simp, hH, fun hA => ht ?_⟩
  unfold thX; rw [hA]; simp

/-- Woodford (2003), Ch. 7 (**the root condition with an extra output weight**): under
`TidyR6bGovRamseyTree.RootOK`, `|z₁| < 1 < |z₂|`, `βz₁z₂ = 1`, `β(z₁ + z₂) = 1 + β + κθ_X`. -/
theorem z_propsX {p : Par} {R : RPar} {γ : ℝ} (hp : p.Std) (hpos : RootOK p R γ) :
    |z1X p R γ| < 1 ∧ 1 < |z2X p R γ| ∧ p.β * z1X p R γ * z2X p R γ = 1 ∧
      p.β * (z1X p R γ + z2X p R γ) = 1 + p.β + p.κ * thX p R γ := by
  have hβ0 := hp.β_pos
  have hβ1 := hp.β_lt_one
  obtain ⟨-, hc⟩ := hpos
  unfold z1X z2X
  set c := p.κ * thX p R γ
  set A := 1 + p.β + c with hA
  set D := A ^ 2 - 4 * p.β with hD
  rcases hc with hc | hc
  · have hA0 : 0 ≤ A := by rw [hA]; linarith
    simp only [hA0, ↓reduceIte]
    have hDpos : (1 - p.β + c) ^ 2 < D := by rw [hD, hA]; nlinarith
    have hD0 : 0 < D := lt_of_le_of_lt (sq_nonneg _) hDpos
    set q := Real.sqrt D with hq
    have hqq : q * q = D := Real.mul_self_sqrt hD0.le
    have hq1 : 1 - p.β + c < q := by rw [hq]; exact Real.lt_sqrt_of_sq_lt hDpos
    have hqA : q < A := by
      rw [hq, Real.sqrt_lt' (by linarith)]; rw [hD]; nlinarith
    have h1 : 0 < (A - q) / (2 * p.β) := by apply div_pos <;> linarith
    have h2 : (A - q) / (2 * p.β) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h3 : 1 < (A + q) / (2 * p.β) := by rw [one_lt_div (by linarith)]; linarith
    refine ⟨by rw [abs_of_pos h1]; exact h2, by rw [abs_of_pos (by linarith)]; exact h3,
      by field_simp; nlinarith, by field_simp; ring⟩
  · have hA0 : ¬ 0 ≤ A := by rw [hA]; linarith
    simp only [hA0, ↓reduceIte]
    have hAneg : A < -(1 + p.β) := by rw [hA]; linarith
    have hDpos : (1 - p.β) ^ 2 < D := by rw [hD]; nlinarith
    have hD0 : 0 < D := lt_of_le_of_lt (sq_nonneg _) hDpos
    set q := Real.sqrt D with hq
    have hqq : q * q = D := Real.mul_self_sqrt hD0.le
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hqA : q < -A := by
      rw [hq, Real.sqrt_lt' (by linarith)]; rw [hD]; nlinarith
    have hq2 : -(A + 2 * p.β) < q := by
      rw [hq]; apply Real.lt_sqrt_of_sq_lt; rw [hD]; nlinarith
    have h1 : (A + q) / (2 * p.β) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    have h2 : -1 < (A + q) / (2 * p.β) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have h3 : (A - q) / (2 * p.β) < -1 := by rw [div_lt_iff₀ (by linarith)]; linarith
    refine ⟨by rw [abs_of_neg h1]; linarith, by rw [abs_of_neg (by linarith)]; linarith,
      by field_simp; nlinarith, by field_simp; ring⟩

/-- Woodford (2003), Ch. 7 and App. A.3: `|1/z₂| < 1`. -/
theorem abs_inv_z2X {p : Par} {R : RPar} {γ : ℝ} (hp : p.Std) (hpos : RootOK p R γ) :
    |1 / z2X p R γ| < 1 := by
  obtain ⟨-, h2, -, -⟩ := z_propsX hp hpos
  rw [abs_div, abs_one, div_lt_one (by linarith)]; exact h2

/-- Woodford (2003), Ch. 7: the root condition holds whenever `A_uG·H > 0`. -/
theorem rootOK_of_pos {p : Par} (R : RPar) (hp : p.Std) {γ : ℝ}
    (hpos : 0 < R.Au * Gw p R * (R.Au * Gw p R - γ)) : RootOK p R γ := by
  have hH : R.Au * Gw p R - γ ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hθ := lt_trans one_pos hp.one_lt_θ
  refine ⟨hH, Or.inl (mul_pos hp.κ_pos ?_)⟩
  have e : thX p R γ = R.Au * Gw p R * (R.Au * Gw p R - γ) * p.θ /
      (R.Au * Gw p R - γ) ^ 2 := by unfold thX; field_simp
  rw [e]; exact div_pos (mul_pos hpos hθ) (by positivity)

/-- Woodford (2003), Ch. 7 (tool): the backward solution with `|c| < 1` is bounded,
`|bwd c f| ≤ A/(1 − |c|)` for `|f| ≤ A`. -/
theorem abs_bwd_le' {X : Type*} (T : LagTree X) {c : ℝ} (hc : |c| < 1) {f : X → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hf : ∀ x, |f x| ≤ A) (x : X) : |bwd T c f x| ≤ A / (1 - |c|) := by
  unfold bwd
  have hc0 := abs_nonneg c
  calc _ ≤ ∑ j ∈ Finset.range (T.depth x + 1), |c| ^ j * A := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hf _) (pow_nonneg hc0 j)
    _ = A * ∑ j ∈ Finset.range (T.depth x + 1), |c| ^ j := by rw [Finset.mul_sum]; ring_nf
    _ ≤ A * (1 - |c|)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        rw [← tsum_geometric_of_lt_one hc0 hc]
        exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hc0 j)
          (summable_geometric_of_lt_one hc0 hc)
    _ = A / (1 - |c|) := by ring

/-! ## The reduction with an extra output weight -/

/-- Woodford (2003), §5: the output condition with the extra weight:
`−Hŷ − A_vΔ̂ + (1−αβ)(σ+ω)λ̂₁ − (1−αβ)(1+ω)μ = r₀`. -/
theorem red_l1X {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (vm v vn : Fin 9 → ℝ) :
    -((R.Au * Gw p R - γ) * v 0) - (1 - R.Φ) * R.Au * v 4 + (1 - p.α * p.β) * (p.σ + p.ω) * v 5 -
      (1 - p.α * p.β) * (1 + p.ω) * (v 5 + v 6) = (DQrX p R γ vm v + DNr p R vn) 0 := by
  have h := red_l1 R hp vm v vn
  simp only [DQrX, Pi.add_apply, Matrix.cons_val_zero] at h ⊢
  linear_combination h

/-- Woodford (2003), §5: the other eight linearised conditions are unchanged. -/
theorem red_otherX (p : Par) (R : RPar) (γ : ℝ) (vm v vn : Fin 9 → ℝ) (i : Fin 9) (hi : i ≠ 0) :
    (DQrX p R γ vm v + DNr p R vn) i = (DQr p R vm v + DNr p R vn) i := by
  have h0 : (![γ * v 0, 0, 0, 0, 0, 0, 0, 0, 0] : Fin 9 → ℝ) i = 0 := by
    fin_cases i <;> simp_all
  rw [DQrX, Pi.add_apply, Pi.add_apply, Pi.add_apply, h0, add_zero]

/-- Woodford (2003), (2.20) linearised with purchases: the price index
(`NonlinearNKMarkovRamseyLin.red_x`). -/
theorem red_xX {p : Par} (R : RPar) (γ : ℝ) (vm v vn : Fin 9 → ℝ) :
    (DQrX p R γ vm v + DNr p R vn) 7 = p.α * (p.θ - 1) * v 1 - (1 - p.α) * (p.θ - 1) *
      ((v 3 - v 2) / p.c0) := by
  rw [red_otherX p R γ vm v vn 7 (by decide)]; exact red_x R vm v vn

/-- Woodford (2003), (2.20) linearised with purchases: the dispersion block
(`NonlinearNKMarkovRamseyLin.red_D`). -/
theorem red_DX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (vm v vn : Fin 9 → ℝ) :
    v 4 = p.α * vm 4 + aE p / (p.θ - 1) * (DQrX p R γ vm v + DNr p R vn) 7 +
      (DQrX p R γ vm v + DNr p R vn) 8 := by
  rw [red_otherX p R γ vm v vn 7 (by decide), red_otherX p R γ vm v vn 8 (by decide)]
  exact red_D R hp vm v vn

/-- Woodford (2003), §5 with purchases: the summed-multiplier block
(`NonlinearNKMarkovRamseyLin.red_mu`). -/
theorem red_muX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (vm v vn : Fin 9 → ℝ) :
    v 5 + v 6 = p.α * (vm 5 + vm 6) + (DQrX p R γ vm v + DNr p R vn) 2 +
      (DQrX p R γ vm v + DNr p R vn) 3 -
        ramseyLam p R 0 * p.c0 / (p.θ - 1) * (DQrX p R γ vm v + DNr p R vn) 7 := by
  rw [red_otherX p R γ vm v vn 2 (by decide), red_otherX p R γ vm v vn 3 (by decide),
    red_otherX p R γ vm v vn 7 (by decide)]
  exact red_mu R hp vm v vn

/-- Woodford (2003), (2.19) linearised with purchases: the NKPC
(`NonlinearNKMarkovRamseyLin.red_pc`). -/
theorem red_pcX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (vm v vn : Fin 9 → ℝ) :
    v 1 = p.κ * v 0 + p.β * vn 1 + (1 - p.α) / (p.c0 * p.α) *
      ((DQrX p R γ vm v + DNr p R vn) 6 - (DQrX p R γ vm v + DNr p R vn) 5) +
        ((DQrX p R γ vm v + DNr p R vn) 7 - p.α * p.β * (p.α * (p.θ - 1) * vn 1 -
          (1 - p.α) * (p.θ - 1) * ((vn 3 - vn 2) / p.c0))) / (p.α * (p.θ - 1)) := by
  rw [red_otherX p R γ vm v vn 6 (by decide), red_otherX p R γ vm v vn 5 (by decide),
    red_otherX p R γ vm v vn 7 (by decide)]
  exact red_pc R hp vm v vn

/-- Woodford (2003), Ch. 7, (1.17) with purchases (**the targeting rule**):
`H(ŷ − ŷ₋) + A_uGθπ` equals the forcing of `NonlinearNKMarkovRamseyLin.red_target`. -/
theorem red_targetX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (vm v vn : Fin 9 → ℝ) (r0m : ℝ)
    (h0m : -((R.Au * Gw p R - γ) * vm 0) - (1 - R.Φ) * R.Au * vm 4 +
      (1 - p.α * p.β) * (p.σ + p.ω) * vm 5 - (1 - p.α * p.β) * (1 + p.ω) * (vm 5 + vm 6) = r0m) :
    (R.Au * Gw p R - γ) * (v 0 - vm 0) + R.Au * Gw p R * p.θ * v 1 =
      (1 - p.α * p.β) * (p.σ + p.ω) * (-((1 - p.α) * aE p / p.c0 *
        ((vm 5 + vm 6) + ramseyLam p R 3 * vm 4)) -
        (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1) *
          (DQrX p R γ vm v + DNr p R vn) 7 + (DQrX p R γ vm v + DNr p R vn) 2 -
        (1 - p.α) / (p.α * p.c0) * (DQrX p R γ vm v + DNr p R vn) 1) -
      ((DQrX p R γ vm v + DNr p R vn) 0 - r0m) - (1 - R.Φ) * R.Au * (v 4 - vm 4) -
      (1 - p.α * p.β) * (1 + p.ω) * ((v 5 + v 6) - (vm 5 + vm 6)) := by
  have e := red_l1X R hp γ vm v vn
  have lag := red_l1_lag R hp vm v vn
  have key := key_theta R hp
  rw [red_otherX p R γ vm v vn 7 (by decide), red_otherX p R γ vm v vn 2 (by decide),
    red_otherX p R γ vm v vn 1 (by decide)]
  linear_combination (-1 : ℝ) * e + h0m + (1 - p.α * p.β) * (p.σ + p.ω) * lag - v 1 * key

/-- Woodford (2003), Ch. 7, §1–2 with purchases (**the commitment system**): at a node where all
nine linearised conditions hold with zero forcing, the previous node's output condition holds and
the expected price-index residual vanishes: `Δ̂ = αΔ̂₋`, `μ = αμ₋`, the NKPC, and the targeting
rule `H(ŷ − ŷ₋) + A_uGθπ = (1−α)[⋯]`. -/
theorem commitment_systemX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (vm v vn : Fin 9 → ℝ)
    (h : DQrX p R γ vm v + DNr p R vn = 0)
    (h0m : -((R.Au * Gw p R - γ) * vm 0) - (1 - R.Φ) * R.Au * vm 4 +
      (1 - p.α * p.β) * (p.σ + p.ω) * vm 5 - (1 - p.α * p.β) * (1 + p.ω) * (vm 5 + vm 6) = 0)
    (h7n : p.α * (p.θ - 1) * vn 1 - (1 - p.α) * (p.θ - 1) * ((vn 3 - vn 2) / p.c0) = 0) :
    v 4 = p.α * vm 4 ∧ v 5 + v 6 = p.α * (vm 5 + vm 6) ∧ v 1 = p.κ * v 0 + p.β * vn 1 ∧
      (R.Au * Gw p R - γ) * (v 0 - vm 0) + R.Au * Gw p R * p.θ * v 1 =
        (1 - p.α) * ((1 - R.Φ) * R.Au * vm 4 +
        (1 - p.α * p.β) * (1 + p.ω) * (vm 5 + vm 6) - (1 - p.α * p.β) * (p.σ + p.ω) *
          (aE p / p.c0) * ((vm 5 + vm 6) + ramseyLam p R 3 * vm 4)) := by
  have hr : ∀ i, (DQrX p R γ vm v + DNr p R vn) i = 0 := fun i => congrFun h i
  have hr' : ∀ i, i ≠ 0 → (DQr p R vm v + DNr p R vn) i = 0 := fun i hi => by
    rw [← red_otherX p R γ vm v vn i hi]; exact hr i
  have hD := red_D R hp vm v vn
  have hμ := red_mu R hp vm v vn
  have hpc := red_pc R hp vm v vn
  have ht := red_targetX R hp γ vm v vn 0 h0m
  rw [hr' 7 (by decide), hr' 8 (by decide)] at hD
  rw [hr' 2 (by decide), hr' 3 (by decide), hr' 7 (by decide)] at hμ
  rw [hr' 6 (by decide), hr' 5 (by decide), hr' 7 (by decide), h7n] at hpc
  simp only [hr, mul_zero, add_zero, sub_zero, zero_div, sub_self] at hD hμ hpc ht
  refine ⟨hD, hμ, hpc, ?_⟩
  rw [hD, hμ] at ht
  linear_combination ht

/-! ## The operator and its inverse -/

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), Ch. 7 and App. A.3: the linearised operator with the extra output weight. -/
noncomputable def LRX (p : Par) (R : RPar) (γ : ℝ) (v : X → Fin 9 → ℝ) (x : X) : Fin 9 → ℝ :=
  DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, targeting-rule forcing `f = F/H`:
`ŷ − ŷ₋ + θ_Xπ = f`. -/
noncomputable def fvX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  Ftv T p R r x / (R.Au * Gw p R - γ)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, forcing of `βMy − (1+β+κθ_X)y + lag y = h`. -/
noncomputable def hvX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  thX p R γ * gv T p r x + p.β * T.M (fvX T p R γ r) x - fvX T p R γ r x

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, the forward factor `u = y − z₁ lag y`. -/
noncomputable def uvX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (1 / z2X p R γ) (fun x => -hvX T p R γ r x / (p.β * z2X p R γ))

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, output: `y = z₁ lag y + u`. -/
noncomputable def yvX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) : X → ℝ :=
  bwd T (z1X p R γ) (uvX T p R γ r)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, inflation from the targeting rule:
`π = (f − y + lag y)/θ_X`. -/
noncomputable def pivX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (fvX T p R γ r x - yvX T p R γ r x + lag0 T (yvX T p R γ r) x) / thX p R γ

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `F̂` forward with root `αβ`. -/
noncomputable def FvX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (p.α * p.β) (fun x => (1 - p.α * p.β) * (1 - p.σ) * yvX T p R γ r x +
    p.α * p.β * (p.θ - 1) * T.M (pivX T p R γ r) x + r x 5)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, the relative price `x̂` from the price
index. -/
noncomputable def xvX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (p.α * (p.θ - 1) * pivX T p R γ r x - r x 7) / ((1 - p.α) * (p.θ - 1))

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₁` from the output condition
(`TidyR6bGovRamseyTree.red_l1X`).
-/
noncomputable def l1vX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (r x 0 + (R.Au * Gw p R - γ) * yvX T p R γ r x + (1 - R.Φ) * R.Au * Dv T p r x +
    (1 - p.α * p.β) * (1 + p.ω) * Muv T p R r x) / ((1 - p.α * p.β) * (p.σ + p.ω))

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₄` forward with root `αβ`. -/
noncomputable def l4vX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (p.α * p.β) (fun x => (1 - R.Φ) * R.Au * yvX T p R γ r x +
    p.α * p.β * ramseyLam p R 3 * aE p * T.M (pivX T p R γ r) x + r x 4)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₃` from the `F̂` condition. -/
noncomputable def l3vX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (r x 2 - (l1vX T p R γ r x + ramseyLam p R 0 * FvX T p R γ r x -
    p.α * (lag0 T (l1vX T p R γ r) x +
    ramseyLam p R 0 * ((p.θ - 1) * pivX T p R γ r x + FvX T p R γ r x))) +
    (1 - p.α) * (aE p / p.c0) * (l4vX T p R γ r x - ramseyLam p R 3 * aE p * xvX T p R γ r x)) /
      ((1 - p.α) * ((p.θ - 1) / p.c0)) + ramseyLam p R 2 * (p.θ - 1) * xvX T p R γ r x

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse with the extra output weight**). -/
noncomputable def LinvRX (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : Fin 9 → ℝ :=
  ![yvX T p R γ r x, pivX T p R γ r x, FvX T p R γ r x, FvX T p R γ r x + p.c0 * xvX T p R γ r x,
    Dv T p r x, l1vX T p R γ r x, Muv T p R r x - l1vX T p R γ r x, l3vX T p R γ r x,
    l4vX T p R γ r x]

/-! ## Uniform bounds -/

/-- Woodford (2003), App. A.3: a bound on the targeting-rule forcing (from
`NonlinearNKMarkovRamseyTree.bd_fv`, since
`f_X = (A_uG/H)f`). -/
theorem bd_fvX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*}
      (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
        ∀ y, |fvX T p R γ r y| ≤ c * A := by
  obtain ⟨c, hc, hb⟩ := bd_fv R hp
  obtain ⟨-, -, hH, hA⟩ := thX_props R hp hpos
  refine ⟨|R.Au * Gw p R / (R.Au * Gw p R - γ)| * c, by positivity, fun T r A hA0 hr y => ?_⟩
  have e : fvX T p R γ r y = R.Au * Gw p R / (R.Au * Gw p R - γ) * fv T p R r y := by
    simp only [fvX, fv]
    rw [div_mul_div_comm, mul_comm (R.Au * Gw p R - γ), mul_div_mul_left _ _ hA]
  rw [e, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb T r A hA0 hr y) (abs_nonneg _)

/-- Woodford (2003), App. A.3: a bound on the forcing of the second-order output equation. -/
theorem bd_hvX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |hvX T p R γ r y| ≤ c * A := by
  obtain ⟨cg, hcg, hg⟩ := bd_gv (p := p)
  obtain ⟨cf, hcf, hf⟩ := bd_fvX R hp γ hpos
  refine ⟨|1| * (|(thX p R γ)| * cg + |p.β| * cf) + |-1| * cf, by positivity,
    fun T r A hA hr y => ?_⟩
  have := lb2 (lb2 (hg T r A hA hr) (lbM T (hf T r A hA hr)) (thX p R γ) p.β) (hf T r A hA hr)
    1 (-1) y
  convert this using 2
  simp only [hvX]; ring

/-- Woodford (2003), App. A.3: a bound on the forward factor `u`, and its equation
`u = (1/z₂)Mu − h/(βz₂)`. -/
theorem bd_uvX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |uvX T p R γ r y| ≤ c * A) ∧ ∀ y, uvX T p R γ r y =
        1 / z2X p R γ * T.M (uvX T p R γ r) y + -hvX T p R γ r y / (p.β * z2X p R γ) := by
  obtain ⟨ch, hch, hh⟩ := bd_hvX R hp γ hpos
  refine ⟨Sg (1 / z2X p R γ) * (|-(1 / (p.β * z2X p R γ))| * ch + |0| * 0), by
    have := Sg_nonneg (1 / z2X p R γ); positivity, fun T r A hA hr => ?_⟩
  have hin := lb2 (g := fun _ => (0 : ℝ)) (cg := 0) (hh T r A hA hr) (fun _ => by simp)
    (-(1 / (p.β * z2X p R γ))) 0
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_inv_z2X hp hpos)
    (A := (|-(1 / (p.β * z2X p R γ))| * ch + |0| * 0) * A)
    (by positivity) (f := fun y => -hvX T p R γ r y / (p.β * z2X p R γ)) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on output, `y = z₁ lag y + u`. -/
theorem bd_yvX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |yvX T p R γ r y| ≤ c * A := by
  obtain ⟨cu, hcu, hu⟩ := bd_uvX R hp γ hpos
  obtain ⟨hz1, -, -, -⟩ := z_propsX hp hpos
  have h1 : 0 < 1 - |z1X p R γ| := by linarith
  refine ⟨cu / (1 - |z1X p R γ|), by positivity, fun T r A hA hr y => ?_⟩
  exact (abs_bwd_le' T hz1 (by positivity) (hu T r A hA hr).1 y).trans
    (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a bound on inflation. -/
theorem bd_pivX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |pivX T p R γ r y| ≤ c * A := by
  obtain ⟨cf, hcf, hf⟩ := bd_fvX R hp γ hpos
  obtain ⟨cy, hcy, hy⟩ := bd_yvX R hp γ hpos
  refine ⟨|1 / (thX p R γ)| * (|1| * (|1| * cf + |-1| * cy) + |1| * cy), by positivity,
    fun T r A hA hr y => ?_⟩
  have hY := hy T r A hA hr
  have := lb2 (lb2 (hf T r A hA hr) hY 1 (-1)) (lbLag T (by positivity) hY) 1 1
  have e := lb2 (g := fun _ => (0 : ℝ)) (cg := 0) this (fun _ => by simp) (1 / thX p R γ) 0 y
  convert e using 2
  · simp only [pivX]; ring
  · ring

/-- Woodford (2003), App. A.3: a bound on `F̂`, and its forward equation. -/
theorem bd_FvX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |FvX T p R γ r y| ≤ c * A) ∧ ∀ y, FvX T p R γ r y = p.α * p.β * T.M (FvX T p R γ r) y +
        ((1 - p.α * p.β) * (1 - p.σ) * yvX T p R γ r y +
          p.α * p.β * (p.θ - 1) * T.M (pivX T p R γ r) y + r y 5) := by
  obtain ⟨cy, hcy, hy⟩ := bd_yvX R hp γ hpos
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivX R hp γ hpos
  set k1 := (1 - p.α * p.β) * (1 - p.σ)
  set k2 := p.α * p.β * (p.θ - 1)
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨Sg (p.α * p.β) * ci, by have := Sg_nonneg (p.α * p.β); positivity,
    fun T r A hA hr => ?_⟩
  have hin := lb2 (lb2 (hy T r A hA hr) (lbM T (hπ T r A hA hr)) k1 k2)
    (f := fun y => k1 * yvX T p R γ r y + k2 * T.M (pivX T p R γ r) y) (g := fun y => r y 5)
    (cg := 1) (fun y => by simpa using hr y 5) 1 1
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_ab hp) (A := ci * A) (by positivity)
    (f := fun y => k1 * yvX T p R γ r y + k2 * T.M (pivX T p R γ r) y + r y 5) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on `λ̂₄`, and its forward equation. -/
theorem bd_l4vX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |l4vX T p R γ r y| ≤ c * A) ∧ ∀ y, l4vX T p R γ r y =
        p.α * p.β * T.M (l4vX T p R γ r) y +
        ((1 - R.Φ) * R.Au * yvX T p R γ r y +
          p.α * p.β * ramseyLam p R 3 * aE p * T.M (pivX T p R γ r) y + r y 4) := by
  obtain ⟨cy, hcy, hy⟩ := bd_yvX R hp γ hpos
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivX R hp γ hpos
  set k1 := (1 - R.Φ) * R.Au
  set k2 := p.α * p.β * ramseyLam p R 3 * aE p
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨Sg (p.α * p.β) * ci, by have := Sg_nonneg (p.α * p.β); positivity,
    fun T r A hA hr => ?_⟩
  have hin := lb2 (lb2 (hy T r A hA hr) (lbM T (hπ T r A hA hr)) k1 k2)
    (f := fun y => k1 * yvX T p R γ r y + k2 * T.M (pivX T p R γ r) y) (g := fun y => r y 4)
    (cg := 1) (fun y => by simpa using hr y 4) 1 1
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_ab hp) (A := ci * A) (by positivity)
    (f := fun y => k1 * yvX T p R γ r y + k2 * T.M (pivX T p R γ r) y + r y 4) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on the relative price `x̂`. -/
theorem bd_xvX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |xvX T p R γ r y| ≤ c * A := by
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivX R hp γ hpos
  set k := 1 / ((1 - p.α) * (p.θ - 1))
  refine ⟨|k * (p.α * (p.θ - 1))| * cπ + |-k| * 1, by positivity, fun T r A hA hr y => ?_⟩
  have := lb2 (hπ T r A hA hr) (g := fun y => r y 7) (cg := 1)
    (fun y => by simpa using hr y 7) (k * (p.α * (p.θ - 1))) (-k) y
  convert this using 2
  simp only [xvX, k]; ring

/-- Woodford (2003), App. A.3: a bound on `λ̂₁`. -/
theorem bd_l1vX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |l1vX T p R γ r y| ≤ c * A := by
  obtain ⟨cy, hcy, hy⟩ := bd_yvX R hp γ hpos
  obtain ⟨cD, hcD, hD⟩ := bd_Dv hp
  obtain ⟨cM, hcM, hM⟩ := bd_Muv R hp
  set k := 1 / ((1 - p.α * p.β) * (p.σ + p.ω))
  set c1 := |k| * 1 + |k * (R.Au * Gw p R - γ)| * cy
  set c2 := |k * ((1 - R.Φ) * R.Au)| * cD + |k * ((1 - p.α * p.β) * (1 + p.ω))| * cM
  refine ⟨|1| * c1 + |1| * c2, by positivity, fun T r A hA hr y => ?_⟩
  have e1 := lb2 (f := fun y => r y 0) (cf := 1) (fun y => by simpa using hr y 0)
    (hy T r A hA hr) k (k * (R.Au * Gw p R - γ))
  have e2 := lb2 (hD T r A hA hr) (hM T r A hA hr) (k * ((1 - R.Φ) * R.Au))
    (k * ((1 - p.α * p.β) * (1 + p.ω)))
  have := lb2 e1 e2 1 1 y
  convert this using 2
  simp only [l1vX, k]; ring

/-- Woodford (2003), App. A.3: a bound on `λ̂₃`. -/
theorem bd_l3vX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |l3vX T p R γ r y| ≤ c * A := by
  obtain ⟨c1, hc1, h1⟩ := bd_l1vX R hp γ hpos
  obtain ⟨cF, hcF, hF⟩ := bd_FvX R hp γ hpos
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivX R hp γ hpos
  obtain ⟨c4, hc4, h4⟩ := bd_l4vX R hp γ hpos
  obtain ⟨cx, hcx, hx⟩ := bd_xvX R hp γ hpos
  set k := 1 / ((1 - p.α) * ((p.θ - 1) / p.c0))
  set L0 := ramseyLam p R 0
  set ka := (1 - p.α) * (aE p / p.c0)
  set La := ramseyLam p R 3 * aE p
  set Lb := ramseyLam p R 2 * (p.θ - 1)
  set d1 := |1| * 1 + |-1| * (|1| * c1 + |L0| * cF)
  set d2 := |1| * c1 + |L0| * (|p.θ - 1| * cπ + |1| * cF)
  set d3 := |1| * c4 + |-La| * cx
  refine ⟨|k| * (|1| * (|1| * d1 + |p.α| * d2) + |ka| * d3) + |Lb| * cx, by positivity,
    fun T r A hA hr y => ?_⟩
  have hl1 := h1 T r A hA hr
  have hFF := (hF T r A hA hr).1
  have e1 := lb2 (f := fun y => r y 2) (cf := 1) (fun y => by simpa using hr y 2)
    (lb2 hl1 hFF 1 L0) 1 (-1)
  have e2 := lb2 (lbLag T (by positivity) hl1) (lb2 (hπ T r A hA hr) hFF (p.θ - 1) 1) 1 L0
  have e12 := lb2 e1 e2 1 p.α
  have e3 := lb2 (h4 T r A hA hr).1 (hx T r A hA hr) 1 (-La)
  have e123 := lb2 e12 e3 1 ka
  have := lb2 e123 (hx T r A hA hr) k Lb y
  convert this using 2
  simp only [l3vX, k, L0, ka, La, Lb]
  field_simp
  ring

/-! ## The inverse is a right inverse -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r`**): for every bounded forcing `r` on
every event tree, the constructed process solves the linearised Ramsey system. -/
theorem LRX_LinvRX {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ)
    (r : X → Fin 9 → ℝ) (A : ℝ) (hA : 0 ≤ A) (hr : ∀ y k, |r y k| ≤ A) :
    LRX T p R γ (LinvRX T p R γ r) = r := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : (thX p R γ) ≠ 0 := (thX_props R hp hpos).1
  obtain ⟨-, hHth, hH, hAG⟩ := thX_props R hp hpos
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨hz1a, hz2a, hzz, hzs⟩ := z_propsX hp hpos
  have hz2 : z2X p R γ ≠ 0 := fun h => by rw [h, abs_zero] at hz2a; linarith
  obtain ⟨_, _, hu⟩ := bd_uvX R hp γ hpos
  obtain ⟨_, _, hF⟩ := bd_FvX R hp γ hpos
  obtain ⟨_, _, h4⟩ := bd_l4vX R hp γ hpos
  have Eu := (hu T r A hA hr).2
  have EF := (hF T r A hA hr).2
  have E4 := (h4 T r A hA hr).2
  set v := LinvRX T p R γ r with hvdef
  set y := yvX T p R γ r
  set π := pivX T p R γ r
  set D := Dv T p r
  set μ := Muv T p R r
  set f := fvX T p R γ r
  -- the scalar equations
  have ED : ∀ x, D x = p.α * lag0 T D x + (aE p / (p.θ - 1) * r x 7 + r x 8) := fun x =>
    bwd_eq T _ _ x
  have EM : ∀ x, μ x = p.α * lag0 T μ x +
      (r x 2 + r x 3 - ramseyLam p R 0 * p.c0 / (p.θ - 1) * r x 7) := fun x => bwd_eq T _ _ x
  have Ey : ∀ x, y x = z1X p R γ * lag0 T y x + uvX T p R γ r x := fun x => bwd_eq T _ _ x
  have E7 : ∀ x, p.α * (p.θ - 1) * π x - (1 - p.α) * (p.θ - 1) * xvX T p R γ r x = r x 7 :=
    fun x => by simp only [xvX, π]; field_simp; ring
  have Et : ∀ x, y x - lag0 T y x + (thX p R γ) * π x = f x := fun x => by
    simp only [π, pivX]; field_simp; ring
  have EMy : ∀ x, T.M (uvX T p R γ r) x = T.M y x - z1X p R γ * y x := fun x => by
    have e : uvX T p R γ r = fun x => 1 * y x + -z1X p R γ * lag0 T y x := by
      funext x; rw [Ey x]; ring
    rw [e, M_lin, M_lag0]; ring
  have EMπ : ∀ x, T.M π x = (T.M f x - T.M y x + y x) / (thX p R γ) := fun x => by
    have e : π = fun x => (1 / thX p R γ) * (1 * f x + -1 * y x) +
        (1 / thX p R γ) * lag0 T y x := by
      funext x; simp only [π, pivX]; ring
    rw [e, M_lin, M_lin, M_lag0]; field_simp; ring
  have Epc : ∀ x, π x = p.κ * y x + p.β * T.M π x + gv T p r x := fun x => by
    have h1 := Eu x
    have h2 := EMy x
    have hhv : hvX T p R γ r x = (thX p R γ) * gv T p r x + p.β * T.M f x - f x := rfl
    have hux : uvX T p R γ r x = y x - z1X p R γ * lag0 T y x := by rw [Ey x]; ring
    rw [EMπ x]
    have ht := Et x
    have key : p.β * T.M y x - (1 + p.β + p.κ * thX p R γ) * y x + lag0 T y x =
        hvX T p R γ r x := by
      rw [h2, hux] at h1
      linear_combination (norm := (field_simp; ring)) (-(p.β * z2X p R γ)) * h1 + y x * hzs -
        lag0 T y x * hzz
    rw [hhv] at key
    linear_combination (norm := (field_simp; ring)) (1 / thX p R γ) * ht + (1 / thX p R γ) * key
  -- the component functions of `v`
  have v0 : (fun z => v z 0) = y := by funext z; simp [hvdef, LinvRX, y]
  have v1 : (fun z => v z 1) = π := by funext z; simp [hvdef, LinvRX, π]
  have v2 : (fun z => v z 2) = FvX T p R γ r := by funext z; simp [hvdef, LinvRX]
  have v3 : (fun z => v z 3) = fun z => 1 * FvX T p R γ r z + p.c0 * xvX T p R γ r z := by
    funext z; simp [hvdef, LinvRX]
  have v4 : (fun z => v z 4) = D := by funext z; simp [hvdef, LinvRX, D]
  have v5 : (fun z => v z 5) = l1vX T p R γ r := by funext z; simp [hvdef, LinvRX]
  have v6 : (fun z => v z 6) = fun z => 1 * μ z + -1 * l1vX T p R γ r z := by
    funext z; simp [hvdef, LinvRX, μ]; ring
  have v7 : (fun z => v z 7) = l3vX T p R γ r := by funext z; simp [hvdef, LinvRX]
  have v8 : (fun z => v z 8) = l4vX T p R γ r := by funext z; simp [hvdef, LinvRX]
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  have hvx : ∀ x k, v x k = (fun z => v z k) x := fun _ _ => rfl
  have E0 : ∀ x, -((R.Au * Gw p R - γ) * y x) - (1 - R.Φ) * R.Au * D x +
      (1 - p.α * p.β) * (p.σ + p.ω) * l1vX T p R γ r x -
        (1 - p.α * p.β) * (1 + p.ω) * μ x = r x 0 := fun x => by
    simp only [l1vX, y, D, μ]; field_simp; ring
  -- the nine components
  set Rr : X → Fin 9 → ℝ := fun x => DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x) with hRr
  have c7 : ∀ x, Rr x 7 = r x 7 := fun x => by
    change (DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x)) 7 = r x 7
    rw [red_xX, hvx x 1, hvx x 2, hvx x 3, v1, v2, v3]
    simp only
    rw [← E7 x]; field_simp; ring
  have c8 : ∀ x, Rr x 8 = r x 8 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl x 4, hvx x 1, hvx x 2, hvx x 3, hvx x 4, v1, v2, v3, v4]
    simp only
    linear_combination (norm := (field_simp; ring)) ED x - aE p / (p.θ - 1) * E7 x
  have c5 : ∀ x, Rr x 5 = r x 5 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm x 1, hm x 2, hvx x 0, hvx x 2, v0, v1, v2]
    linear_combination EF x
  have c4 : ∀ x, Rr x 4 = r x 4 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm x 1, hm x 8, hvx x 0, hvx x 8, v0, v1, v8]
    linear_combination E4 x
  have c0 : ∀ x, Rr x 0 = r x 0 := fun x => by
    change (DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x)) 0 = r x 0
    rw [← red_l1X R hp γ, hvx x 0, hvx x 4, hvx x 5, hvx x 6, v0, v4, v5, v6]
    simp only
    linear_combination E0 x
  have c2 : ∀ x, Rr x 2 = r x 2 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl x 5, hvx x 1, hvx x 2, hvx x 3, hvx x 5, hvx x 7, hvx x 8, v1, v2, v3, v5, v7, v8]
    simp only [l3vX]
    field_simp
    ring
  have c3 : ∀ x, Rr x 3 = r x 3 := fun x => by
    have h := red_muX R hp γ (lagv T v x) (v x) (Mv T.M v x)
    rw [hl x 5, hl x 6, hvx x 5, hvx x 6, v5, v6, lag0_lin] at h
    simp only at h
    have h2 := c2 x
    have h7 := c7 x
    simp only [hRr] at h2 h7 ⊢
    rw [h2, h7] at h
    linear_combination (-1 : ℝ) * h + EM x
  have c6 : ∀ x, Rr x 6 = r x 6 := fun x => by
    have h := red_pcX R hp γ (lagv T v x) (v x) (Mv T.M v x)
    have h5 := c5 x
    have h7 := c7 x
    simp only [hRr] at h5 h7 ⊢
    rw [h5, h7, hm x 1, hm x 2, hm x 3, hvx x 0, hvx x 1, v0, v1, v2, v3, M_lin] at h
    have hm7 : p.α * (p.θ - 1) * T.M π x - (1 - p.α) * (p.θ - 1) *
        ((1 * T.M (FvX T p R γ r) x + p.c0 * T.M (xvX T p R γ r) x -
          T.M (FvX T p R γ r) x) / p.c0) =
          T.M (fun z => r z 7) x := by
      have e : (fun z => r z 7) = fun z => (p.α * (p.θ - 1)) * π z +
          (-(1 - p.α) * (p.θ - 1)) * xvX T p R γ r z := by
        funext z; rw [← E7 z]; ring
      rw [e, M_lin]; field_simp; ring
    rw [hm7] at h
    have hg := Epc x
    simp only [gv] at hg
    have hk : (1 - p.α) / (p.c0 * p.α) ≠ 0 := div_ne_zero h1α (mul_ne_zero hc0 hα)
    have key : (1 - p.α) / (p.c0 * p.α) * (Rr x 6 - r x 6) = 0 := by
      simp only [hRr]
      linear_combination hg - h
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  have c1 : ∀ x, Rr x 1 = r x 1 := fun x => by
    have h0m : -((R.Au * Gw p R - γ) * lagv T v x 0) - (1 - R.Φ) * R.Au * lagv T v x 4 +
        (1 - p.α * p.β) * (p.σ + p.ω) * lagv T v x 5 -
          (1 - p.α * p.β) * (1 + p.ω) * (lagv T v x 5 + lagv T v x 6) =
            lag0 T (fun z => r z 0) x := by
      simp only [lagv, lag0]
      split_ifs
      · ring
      · have := c0 (T.par x)
        change (DQrX p R γ (lagv T v (T.par x)) (v (T.par x)) +
          DNr p R (Mv T.M v (T.par x))) 0 = r (T.par x) 0 at this
        rw [← red_l1X R hp γ] at this
        exact this
    have h := red_targetX R hp γ (lagv T v x) (v x) (Mv T.M v x) _ h0m
    have h2 := c2 x
    have h7 := c7 x
    have h0 := c0 x
    simp only [hRr] at h2 h7 h0 ⊢
    rw [h2, h7, h0, hl x 0, hl x 4, hl x 5, hl x 6, hvx x 0, hvx x 1, hvx x 4, hvx x 5,
      hvx x 6, v0, v1, v4, v5, v6, lag0_lin] at h
    simp only at h
    have ht := Et x
    have hF : (R.Au * Gw p R - γ) * f x = Ftv T p R r x := by
      rw [show f x = Ftv T p R r x / (R.Au * Gw p R - γ) from rfl, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hH
    simp only [Ftv] at hF
    have hk : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hab hωσ) (div_ne_zero h1α (mul_ne_zero hα hc0))
    have key : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) *
        (Rr x 1 - r x 1) = 0 := by
      simp only [hRr]
      linear_combination h - (R.Au * Gw p R - γ) * ht - hF + π x * hHth
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  funext x i
  fin_cases i
  exacts [c0 x, c1 x, c2 x, c3 x, c4 x, c5 x, c6 x, c7 x, c8 x]


/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity: the a-priori bound with predetermined
variables**): on every event tree, a bounded solution of the homogeneous linearised Ramsey
system with zero initial lag is zero. -/
theorem LRX_inj {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ)
    (v : X → Fin 9 → ℝ) (B : ℝ) (hB : ∀ x k, |v x k| ≤ B) (h0 : LRX T p R γ v = 0) : v = 0 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : (thX p R γ) ≠ 0 := (thX_props R hp hpos).1
  obtain ⟨-, hHth, hH, hAG⟩ := thX_props R hp hpos
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨hz1a, hz2a, hzz, hzs⟩ := z_propsX hp hpos
  have hz2 : z2X p R γ ≠ 0 := fun h => by rw [h, abs_zero] at hz2a; linarith
  have hR : ∀ x, DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x) = 0 := fun x =>
    congrFun h0 x
  have hRk : ∀ x k, (DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x)) k = 0 := fun x k => by
    rw [hR x]; rfl
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  -- the predetermined block
  have hD : ∀ x, v x 4 = 0 := zero_of_eq_lag T (c := p.α) fun x => by
    have := red_DX R hp γ (lagv T v x) (v x) (Mv T.M v x)
    rw [hRk, hRk, hl] at this; simpa using this
  have hμ : ∀ x, v x 5 + v x 6 = 0 := zero_of_eq_lag T (c := p.α) (g := fun z => v z 5 + v z 6)
    fun x => by
      have := red_muX R hp γ (lagv T v x) (v x) (Mv T.M v x)
      rw [hRk, hRk, hRk, hl, hl] at this
      have e := lag0_lin T 1 1 (fun z => v z 5) (fun z => v z 6) x
      simp only [one_mul] at e
      simp only [e]; linarith
  have hDf : (fun z => v z 4) = fun _ => 0 := funext hD
  have hμf : (fun z => v z 5 + v z 6) = fun _ => 0 := funext hμ
  -- the expected price-index residual vanishes
  have h7f : (fun z => p.α * (p.θ - 1) * v z 1 - (1 - p.α) * (p.θ - 1) * ((v z 3 - v z 2) /
      p.c0)) = fun _ => 0 := by
    funext z
    rw [← red_xX R γ (lagv T v z) (v z) (Mv T.M v z)]
    exact hRk z 7
  have hm7 : ∀ x, p.α * (p.θ - 1) * Mv T.M v x 1 - (1 - p.α) * (p.θ - 1) *
      ((Mv T.M v x 3 - Mv T.M v x 2) / p.c0) = 0 := fun x => by
    have e : (fun z => p.α * (p.θ - 1) * v z 1 - (1 - p.α) * (p.θ - 1) * ((v z 3 - v z 2) /
        p.c0)) = fun z => (p.α * (p.θ - 1)) * v z 1 + (-(1 - p.α) * (p.θ - 1) / p.c0) *
          (1 * v z 3 + -1 * v z 2) := by funext z; field_simp; ring
    have := congrFun (congrArg T.M h7f) x
    rw [e, M_lin, M_lin, M_const] at this
    rw [hm, hm, hm]
    simp only at this
    linear_combination (norm := (field_simp; ring)) this
  -- the output condition at the parent
  have h0m : ∀ x, -((R.Au * Gw p R - γ) * lagv T v x 0) - (1 - R.Φ) * R.Au * lagv T v x 4 +
      (1 - p.α * p.β) * (p.σ + p.ω) * lagv T v x 5 -
        (1 - p.α * p.β) * (1 + p.ω) * (lagv T v x 5 + lagv T v x 6) = 0 := fun x => by
    simp only [lagv, lag0]
    split_ifs
    · ring
    · have := red_l1X R hp γ (lagv T v (T.par x)) (v (T.par x)) (Mv T.M v (T.par x))
      rw [hRk] at this; exact this
  have hcs := fun x => commitment_systemX R hp γ (lagv T v x) (v x) (Mv T.M v x) (hR x) (h0m x)
    (hm7 x)
  -- the commitment block
  set y : X → ℝ := fun z => v z 0 with hy
  set π : X → ℝ := fun z => v z 1 with hπ
  have Et : ∀ x, y x - lag0 T y x + (thX p R γ) * π x = 0 := fun x => by
    obtain ⟨-, -, -, h4⟩ := hcs x
    rw [hl, hl, hl, hl, hDf, lag0_zero] at h4
    have e := lag0_lin T 1 1 (fun z => v z 5) (fun z => v z 6) x
    simp only [one_mul] at e
    rw [← e, hμf, lag0_zero] at h4
    simp only [mul_zero, add_zero, sub_zero] at h4
    have h5 : (R.Au * Gw p R - γ) * (y x - lag0 T y x + thX p R γ * π x) = 0 := by
      linear_combination h4 + π x * hHth
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h hH
    · exact h
  have Epc : ∀ x, π x = p.κ * y x + p.β * T.M π x := fun x => by
    obtain ⟨-, -, h3, -⟩ := hcs x
    rw [hm] at h3; exact h3
  have hyB : ∀ x, |y x| ≤ B := fun x => hB x 0
  have hπf : π = fun z => (-1 / (thX p R γ)) * y z + (1 / thX p R γ) * lag0 T y z := by
    funext z; have := Et z; field_simp; linarith
  have hMπ : ∀ x, T.M π x = (-1 / (thX p R γ)) * (T.M y x - y x) := fun x => by
    rw [hπf, M_lin, M_lag0]; ring
  have key : ∀ x, p.β * T.M y x - (1 + p.β + p.κ * thX p R γ) * y x + lag0 T y x = 0 := fun x => by
    have h1 := Epc x
    rw [hMπ x, hπf] at h1
    simp only at h1
    linear_combination (norm := (field_simp; ring)) (thX p R γ) * h1
  have hu : ∀ x, y x - z1X p R γ * lag0 T y x = 0 := by
    have hlB : ∀ x, |lag0 T y x| ≤ |B| :=
      abs_lag0_le T (abs_nonneg B) fun x => (hyB x).trans (le_abs_self B)
    refine zero_of_eq_cM T (abs_inv_z2X hp hpos) (A := |B| + |z1X p R γ| * |B|)
      (g := fun z => y z - z1X p R γ * lag0 T y z) (fun x => ?_) (fun x => ?_)
    · refine (abs_sub _ _).trans (add_le_add ((hyB x).trans (le_abs_self B)) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hlB x) (abs_nonneg _)
    · have e : (fun z => y z - z1X p R γ * lag0 T y z) =
          fun z => 1 * y z + -z1X p R γ * lag0 T y z := by
        funext z; ring
      rw [e, M_lin, M_lag0]
      simp only
      linear_combination (norm := (field_simp; ring)) (-1 / (p.β * z2X p R γ)) * key x +
        (y x / (p.β * z2X p R γ)) * hzs - (lag0 T y x / (p.β * z2X p R γ)) * hzz
  have hy0 : ∀ x, v x 0 = 0 := zero_of_eq_lag T (c := z1X p R γ) (g := y) fun x => by
    linarith [hu x]
  have hyf : (fun z => v z 0) = fun _ => 0 := funext hy0
  have hπ0 : ∀ x, v x 1 = 0 := fun x => by
    have := Et x
    have e1 : y x = 0 := hy0 x
    have e2 : lag0 T y x = 0 := by rw [show y = fun _ => 0 from hyf, lag0_zero]
    have h2 : (thX p R γ) * π x = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hθ0
    · exact h
  have hπf0 : (fun z => v z 1) = fun _ => 0 := funext hπ0
  have hF0 : ∀ x, v x 2 = 0 := by
    refine zero_of_eq_cM T (abs_ab hp) (A := B) (g := fun z => v z 2) (fun x => hB x 2)
      fun x => ?_
    have := hRk x 5
    simp only [DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val, hm, hπf0, M_const, hy0] at this
    linear_combination this
  have hK0 : ∀ x, v x 3 = 0 := fun x => by
    have := hRk x 7
    rw [red_xX, hπ0, hF0] at this
    have h2 : (1 - p.α) * (p.θ - 1) / p.c0 * v x 3 = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (div_ne_zero (mul_ne_zero h1α hθ) hc0)
    · exact h
  have hl10 : ∀ x, v x 5 = 0 := fun x => by
    have := red_l1X R hp γ (lagv T v x) (v x) (Mv T.M v x)
    rw [hRk, hy0, hD, hμ] at this
    have h2 : (1 - p.α * p.β) * (p.σ + p.ω) * v x 5 = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero hab hωσ)
    · exact h
  have hl20 : ∀ x, v x 6 = 0 := fun x => by linarith [hμ x, hl10 x]
  have hl40 : ∀ x, v x 8 = 0 := by
    refine zero_of_eq_cM T (abs_ab hp) (A := B) (g := fun z => v z 8) (fun x => hB x 8)
      fun x => ?_
    have := hRk x 4
    simp only [DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val, hm, hπf0, M_const, hy0] at this
    linear_combination this
  have hl30 : ∀ x, v x 7 = 0 := fun x => by
    have := hRk x 2
    simp only [DQrX, DQr, Pi.add_apply, Matrix.cons_val, hl, lag0_zero, hπ0, hF0, hK0, hl10,
      hl40, DNr] at this
    have h2 : (1 - p.α) * ((p.θ - 1) / p.c0) * v x 7 = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero h1α (div_ne_zero hθ hc0))
    · exact h
  funext x k
  fin_cases k
  exacts [hy0 x, hπ0 x, hF0 x, hK0 x, hD x, hl10 x, hl20 x, hl30 x, hl40 x]

/-- Woodford (2003), App. A.3 (**the uniform bound on the inverse**): `‖L⁻¹r‖ ≤ K‖r‖` with `K`
depending only on the parameters, for every event tree. -/
theorem LinvRX_bound {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hpos : RootOK p R γ) : ∃ K, 0 ≤ K ∧ ∀ {Y : Type*}
    (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y, ‖r y‖ ≤ A) →
      ∀ y, ‖LinvRX T p R γ r y‖ ≤ K * A := by
  obtain ⟨c0, h0, b0⟩ := bd_yvX R hp γ hpos
  obtain ⟨c1, h1, b1⟩ := bd_pivX R hp γ hpos
  obtain ⟨c2, h2, b2⟩ := bd_FvX R hp γ hpos
  obtain ⟨cx, hx, bx⟩ := bd_xvX R hp γ hpos
  obtain ⟨c4, h4, b4⟩ := bd_Dv hp
  obtain ⟨c5, h5, b5⟩ := bd_l1vX R hp γ hpos
  obtain ⟨cμ, hμ, bμ⟩ := bd_Muv R hp
  obtain ⟨c7, h7, b7⟩ := bd_l3vX R hp γ hpos
  obtain ⟨c8, h8, b8⟩ := bd_l4vX R hp γ hpos
  set K := c0 + c1 + c2 + (c2 + |p.c0| * cx) + c4 + c5 + (cμ + c5) + c7 + c8 with hK
  refine ⟨K, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ y k, |r y k| ≤ A := fun y k => by
    have := (norm_le_pi_norm (r y) k).trans (hr y); rwa [Real.norm_eq_abs] at this
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hc : ∀ c, 0 ≤ c → c * A ≤ K * A → ∀ t : ℝ, |t| ≤ c * A → |t| ≤ K * A :=
    fun c _ hcK t ht => ht.trans hcK
  have hKA : ∀ c, c ≤ K → c * A ≤ K * A := fun c hcK => mul_le_mul_of_nonneg_right hcK hA
  fin_cases i <;> simp only [LinvRX, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact (b0 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b1 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact ((b2 T r A hA hr').1 y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · have e := lb2 (b2 T r A hA hr').1 (bx T r A hA hr') 1 p.c0 y
    simp only [one_mul, abs_one] at e
    exact e.trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b4 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b5 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · have e := lb2 (bμ T r A hA hr') (b5 T r A hA hr') 1 (-1) y
    simp only [one_mul, abs_one, abs_neg, neg_one_mul, ← sub_eq_add_neg] at e
    exact e.trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b7 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact ((b8 T r A hA hr').1 y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))

end Woodford.StabilizationWelfare.TidyR6bGovRamseyTree
