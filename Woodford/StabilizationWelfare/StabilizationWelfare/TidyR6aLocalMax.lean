/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6aGap
import StabilizationWelfare.TidyR6aLargePhi

/-!
# The nonlinear date-0 Ramsey plan is a strict local maximum of welfare

Woodford (2003), *Interest and Prices*, Chapter 6, §2.2, pp. 396–401 and §5 (the second-order
conditions for the Ramsey problem), Chapter 7, §1–§2 (the date-0 Ramsey problem on event trees)
and Appendix E (the second-order expansion of welfare).

Main result **`local_max`**: for the efficient-frame economy `R0 A`, there are `δ > 0` and
`c > 0` such that, whenever the date-0 Ramsey plan `w` (bounded, solving the exact Ramsey
conditions `RamseyL` with the date-0 root lag `lagD0 Δ₋₁`) lies within `ε ≤ δ` of the efficient
steady state at every node, every bounded feasible plan `r` whose output, inflation, `F̂`, `K̂`
and dispersion are within `ρ ≤ δ` of `w` at every node satisfies, at every root `x₀`,

  `W(r)(x₀) ≤ W(w)(x₀) − c · S[‖r − w‖²](x₀)`,

with `‖h‖² = ŷ² + π² + F̂² + K̂² + Δ̂² + Δ̂₋₁²` (`nrm`) and `S` the expected discounted sum. This is
the exact strict local maximality of the nonlinear date-0 plan: coercivity of the Hessian in the
discounted `ℓ²` norm on the tangent space, with the cubic remainder controlled in the sup-norm
neighbourhood. The neighbourhood must be a sup-norm one: the constraints are exponential in the
plan, and the remainder of the Lagrangian density is cubic only pointwise (`R2_bound`).

The proof: `welfare_diff` writes the welfare gap as the discounted sum of the exact node
remainder `R2`; `R2_bound` and `H0_le` reduce it to the Hessian, which is negative definite in
`(ŷ, π)` (`R2_le`); feasibility controls the remaining directions in the discounted `ℓ²` norm,
the dispersion gap through a backward relation (`gap_D`, of order `η²`) and the `F̂` gap through a
forward relation (`gap_F`).
-/

namespace Woodford.StabilizationWelfare.TidyR6aLocalMax

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyTree TidyR5RamseyWeighted
open NonlinearNKMarkovRamseyLin
open TidyR5RamseyDate0 TidyR6aTreeSum TidyR6aLagr TidyR6aHess TidyR6aFeas TidyR6aGap TidyR6aExpand
open TidyR6aLargePhi

/-! ## Constants -/

/-- Woodford (2003), App. A.3: `q = α²β < 1`, the contraction factor of the dispersion law in the
discounted `ℓ²` norm. -/
noncomputable def qA (p : Par) : ℝ := p.α ^ 2 * p.β

/-- Woodford (2003), App. A.3: the Young weight `κ = (1−q)/(4q)`. -/
noncomputable def kapA (p : Par) : ℝ := (1 - qA p) / (4 * qA p)

/-- Woodford (2003), App. A.3: the contraction margin `m = (1−q)/8`. -/
noncomputable def mA (p : Par) : ℝ := (1 - qA p) / 8

/-- Woodford (2003), App. A.3: the discounted `ℓ²` constant `(1 + 1/κ)/m`. -/
noncomputable def QA (p : Par) : ℝ := (1 + 1 / kapA p) / mA p

/-- Woodford (2003), Ch. 3, (2.20): the reset-gap constant `3α/(1−α)` (`price_gap`). -/
noncomputable def C1 (p : Par) : ℝ := 3 * p.α / (1 - p.α)

/-- Woodford (2003), Ch. 6, (2.13): the dispersion-gap constant `6a + 5a² + 5a(θ−1)`. -/
noncomputable def Cd (p : Par) : ℝ := 6 * aE p + 5 * aE p ^ 2 + 5 * aE p * (p.θ - 1)

/-- Woodford (2003), App. A.3: `0 < q < 1`. -/
theorem qA_bounds {p : Par} (hp : p.Std) : 0 < qA p ∧ qA p < 1 := by
  have hα := hp.α_pos
  have hα1 := hp.α_lt_one
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  unfold qA
  refine ⟨by positivity, ?_⟩
  have : p.α ^ 2 < 1 := by nlinarith
  nlinarith

/-- Woodford (2003), App. A.3: the constants are positive. -/
theorem consts_pos {p : Par} (hp : p.Std) :
    0 < kapA p ∧ 0 < mA p ∧ 0 < QA p ∧ 0 ≤ C1 p ∧ 0 ≤ Cd p := by
  obtain ⟨hq0, hq1⟩ := qA_bounds hp
  have hk : 0 < kapA p := by unfold kapA; apply div_pos <;> linarith
  have hm : 0 < mA p := by unfold mA; linarith
  have h1α : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  have hb : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have ha : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  refine ⟨hk, hm, by unfold QA; positivity, by unfold C1; have := hp.α_pos; positivity,
    by unfold Cd; positivity⟩

/-! ## Discounted sums of combinations -/

variable {Y : Type*} (T : LagTree Y)

/-- Woodford (2003), §1: `S[c f] = c S[f]`. -/
theorem S_smul {β : ℝ} (hβ : |β| < 1) {f : Y → ℝ} (hf : Bdd f) (c : ℝ) (x : Y) :
    S T β (fun y => c * f y) x = c * S T β f x := by
  have := congrFun (S_lin T hβ hf hf c 0) x
  simpa using this

/-- Woodford (2003), §1: `S[f + g] = S[f] + S[g]`. -/
theorem S_add {β : ℝ} (hβ : |β| < 1) {f g : Y → ℝ} (hf : Bdd f) (hg : Bdd g) (x : Y) :
    S T β (fun y => f y + g y) x = S T β f x + S T β g x := by
  have := congrFun (S_lin T hβ hf hg 1 1) x
  simpa using this

/-- Woodford (2003), §1: the discounted sum of a five-term combination. -/
theorem S_comb5 {β : ℝ} (hβ : |β| < 1) {f0 f1 f2 f3 f4 : Y → ℝ} (h0 : Bdd f0) (h1 : Bdd f1)
    (h2 : Bdd f2) (h3 : Bdd f3) (h4 : Bdd f4) (c0 c1 c2 c3 c4 : ℝ) (x : Y) :
    S T β (fun y => c0 * f0 y + c1 * f1 y + c2 * f2 y + c3 * f3 y + c4 * f4 y) x =
      c0 * S T β f0 x + c1 * S T β f1 x + c2 * S T β f2 x + c3 * S T β f3 x +
        c4 * S T β f4 x := by
  have b01 : Bdd (fun y => c0 * f0 y + c1 * f1 y) := h0.lin h1 c0 c1
  have b012 : Bdd (fun y => c0 * f0 y + c1 * f1 y + c2 * f2 y) :=
    (b01.lin h2 1 c2).congr fun y => by ring
  have b0123 : Bdd (fun y => c0 * f0 y + c1 * f1 y + c2 * f2 y + c3 * f3 y) :=
    (b012.lin h3 1 c3).congr fun y => by ring
  have s4 : Bdd (fun y => c4 * f4 y) := (h4.lin h4 c4 0).congr fun y => by ring
  have s3 : Bdd (fun y => c3 * f3 y) := (h3.lin h3 c3 0).congr fun y => by ring
  have s2 : Bdd (fun y => c2 * f2 y) := (h2.lin h2 c2 0).congr fun y => by ring
  rw [S_add T hβ b0123 s4, S_add T hβ b012 s3, S_add T hβ b01 s2,
    congrFun (S_lin T hβ h0 h1 c0 c1) x, S_smul T hβ h2, S_smul T hβ h3, S_smul T hβ h4]

omit T in
/-- Bounded functions: squares. -/
theorem bdd_sq {f : Y → ℝ} (hf : Bdd f) : Bdd (fun y => f y ^ 2) :=
  (hf.mul hf).congr fun y => by ring

/-! ## The feasible directions in the discounted `ℓ²` norm -/

/-- **Woodford (2003), Ch. 6, §2.2 (the `F̂` gap is controlled by output and inflation).** For two
bounded feasible plans within `η` of the efficient steady state (`θη ≤ 1/40`,
`(|1−σ| + σ + 1)η ≤ 1`, `5θη ≤ (1−q)/8`), at every node
`S[h_F²] ≤ Q(72(1−σ)²S[h₀²] + 8α²β(θ−1)²S[h₁²])`. -/
theorem gap_F {p : Par} (hp : p.Std) {e : Y → Fin 5 → ℝ} {w r : Y → Fin 9 → ℝ} (hw : VBdd w)
    (hr : VBdd r) {Dm1 : ℝ} (hFw : Feas T p e Dm1 w) (hFr : Feas T p e Dm1 r) {η : ℝ}
    (hθη : p.θ * η ≤ 1 / 40) (hU : (|1 - p.σ| + p.σ + 1) * η ≤ 1)
    (ht : 5 * p.θ * η ≤ (1 - qA p) / 8)
    (hb : ∀ y, |e y 1| ≤ η ∧ |e y 2| ≤ η ∧ |w y 0| ≤ η ∧ |w y 1| ≤ η ∧ |w y 2| ≤ η ∧
      |r y 0 - w y 0| ≤ η ∧ |r y 1 - w y 1| ≤ η ∧ |r y 2 - w y 2| ≤ η) (x : Y) :
    S T p.β (fun y => (r y 2 - w y 2) ^ 2) x ≤ QA p * (72 * (1 - p.σ) ^ 2 *
      S T p.β (fun y => (r y 0 - w y 0) ^ 2) x + 8 * p.α ^ 2 * p.β * (p.θ - 1) ^ 2 *
        S T p.β (fun y => (r y 1 - w y 1) ^ 2) x) := by
  obtain ⟨hq0, hq1⟩ := qA_bounds hp
  obtain ⟨hk, hm, hQ, -, -⟩ := consts_pos hp
  have hβ0 := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hβ : |p.β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hab0 : 0 < p.α * p.β := mul_pos hp.α_pos hβ0
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hb x).1
  have hθ1 := hp.one_lt_θ
  have ht0 : 0 ≤ 5 * p.θ * η := by positivity
  have hg0 := bdd_gap hw hr 0
  have hg1 := bdd_gap hw hr 1
  have hg2 := bdd_gap hw hr 2
  have hv : Bdd (fun y => 6 * |1 - p.σ| * |r y 0 - w y 0| +
      2 * p.α * p.β * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) y) :=
    (bdd_abs hg0).lin ((bdd_abs hg1).M T) _ _
  have hmar := margin hq0 hq1 ht0 ht
  have hκβ : (1 + kapA p) * (p.α * p.β + p.α * p.β * (5 * p.θ * η)) ^ 2 ≤
      p.β * ((1 - 5 * p.θ * η) ^ 2 - mA p) := by
    have e : (1 + kapA p) * (p.α * p.β + p.α * p.β * (5 * p.θ * η)) ^ 2 =
        p.β * ((1 + (1 - qA p) / (4 * qA p)) * qA p * (1 + 5 * p.θ * η) ^ 2) := by
      unfold kapA qA; ring
    rw [e]; unfold mA
    exact mul_le_mul_of_nonneg_left hmar hβ0.le
  have hF := fwd_sq' T hβ0 hβ1 hab0.le (by linarith) hk hm hκβ hg2 hv
    (F_rel T hp hw hr hFw hFr hθη hU hb) x
  -- the source term
  have hM2 : Bdd (T.M (fun y => (r y 1 - w y 1) ^ 2)) := (bdd_sq hg1).M T
  have pt : ∀ y, (6 * |1 - p.σ| * |r y 0 - w y 0| +
      2 * p.α * p.β * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) y) ^ 2 ≤
      72 * (1 - p.σ) ^ 2 * (r y 0 - w y 0) ^ 2 +
        8 * (p.α * p.β) ^ 2 * (p.θ - 1) ^ 2 * T.M (fun y => (r y 1 - w y 1) ^ 2) y := by
    intro y
    have hJ := M_sq_le T (bdd_abs hg1) y
    simp only [sq_abs] at hJ
    have h2 : (6 * |1 - p.σ| * |r y 0 - w y 0| +
        2 * p.α * p.β * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) y) ^ 2 ≤
        2 * (6 * |1 - p.σ| * |r y 0 - w y 0|) ^ 2 +
          2 * (2 * p.α * p.β * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) y) ^ 2 := by
      nlinarith [sq_nonneg (6 * |1 - p.σ| * |r y 0 - w y 0| -
        2 * p.α * p.β * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) y)]
    have e1 : (6 * |1 - p.σ| * |r y 0 - w y 0|) ^ 2 = 36 * (1 - p.σ) ^ 2 * (r y 0 - w y 0) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
    have e2 : (2 * p.α * p.β * (p.θ - 1) * T.M (fun y => |r y 1 - w y 1|) y) ^ 2 =
        4 * (p.α * p.β) ^ 2 * (p.θ - 1) ^ 2 * T.M (fun y => |r y 1 - w y 1|) y ^ 2 := by ring
    have h3 := mul_le_mul_of_nonneg_left hJ
      (by positivity : (0 : ℝ) ≤ 8 * (p.α * p.β) ^ 2 * (p.θ - 1) ^ 2)
    rw [e1, e2] at h2
    linarith
  have hS1 := S_mono T hβ0.le hβ1 (bdd_sq hv) ((bdd_sq hg0).lin hM2 _ _) pt x
  rw [congrFun (S_lin T hβ (bdd_sq hg0) hM2 _ _) x] at hS1
  have hS2 := S_M_le T hβ0 hβ1 (bdd_sq hg1) (fun y => sq_nonneg _) x
  have hS3 := mul_le_mul_of_nonneg_left hS2
    (by positivity : (0 : ℝ) ≤ 8 * (p.α * p.β) ^ 2 * (p.θ - 1) ^ 2)
  have e3 : 8 * (p.α * p.β) ^ 2 * (p.θ - 1) ^ 2 * (S T p.β (fun y => (r y 1 - w y 1) ^ 2) x / p.β)
      = 8 * p.α ^ 2 * p.β * (p.θ - 1) ^ 2 * S T p.β (fun y => (r y 1 - w y 1) ^ 2) x := by
    field_simp
  have hQ' : (1 + 1 / kapA p) / mA p = QA p := rfl
  rw [hQ'] at hF
  calc _ ≤ _ := hF
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hQ.le

/-- **Woodford (2003), Ch. 6, (2.12)–(2.13), p. 400 (the dispersion gap is of order `η`).** For
two bounded feasible plans within `η` of the efficient steady state (`aη, (θ−1)η ≤ 1/10`,
`4aη ≤ (1−q)/8`), at every root `S[h_Δ²] ≤ Q(C_d(1 + C₁))²η²S[h₁²]`. -/
theorem gap_D {p : Par} (hp : p.Std) {e : Y → Fin 5 → ℝ} {w r : Y → Fin 9 → ℝ} (hw : VBdd w)
    (hr : VBdd r) {Dm1 : ℝ} (hFw : Feas T p e Dm1 w) (hFr : Feas T p e Dm1 r) {η : ℝ}
    (haη : aE p * η ≤ 1 / 10) (hbη : (p.θ - 1) * η ≤ 1 / 10) (ht : 4 * aE p * η ≤ (1 - qA p) / 8)
    (hb : ∀ y, |w y 1| ≤ η ∧ |xr p (w y)| ≤ η ∧ |r y 1 - w y 1| ≤ η ∧
      |xr p (r y) - xr p (w y)| ≤ η ∧ |lagDv T Dm1 w y - 1| ≤ η) {x : Y} (hx : T.depth x = 0) :
    S T p.β (fun y => (r y 4 - w y 4) ^ 2) x ≤
      QA p * (Cd p * (1 + C1 p)) ^ 2 * η ^ 2 * S T p.β (fun y => (r y 1 - w y 1) ^ 2) x := by
  obtain ⟨hq0, hq1⟩ := qA_bounds hp
  obtain ⟨hk, hm, hQ, -, -⟩ := consts_pos hp
  have hβ0 := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hβ : |p.β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hα := hp.α_pos
  have ha : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hb x).1
  have ht0 : 0 ≤ 4 * aE p * η := by positivity
  have hg1 := bdd_gap hw hr 1
  have hg4 := bdd_gap hw hr 4
  have hk' : ∀ y, |p.α * Real.exp (aE p * r y 1)| ≤ p.α * (1 + 4 * aE p * η) := by
    intro y
    obtain ⟨h1, -, h3, -, -⟩ := hb y
    have hr1 : |r y 1| ≤ 2 * η := by
      have := abs_add_le (w y 1) (r y 1 - w y 1)
      rw [show w y 1 + (r y 1 - w y 1) = r y 1 by ring] at this; linarith
    have hu : |aE p * r y 1| ≤ 2 * aE p * η := by
      rw [abs_mul, abs_of_pos ha]; nlinarith
    have h4 := Real.abs_exp_sub_one_le (x := aE p * r y 1) (by linarith)
    rw [abs_mul, abs_of_pos hα, abs_of_pos (Real.exp_pos _)]
    have : Real.exp (aE p * r y 1) ≤ 1 + 4 * aE p * η := by
      have := le_abs_self (Real.exp (aE p * r y 1) - 1); linarith
    exact mul_le_mul_of_nonneg_left this hα.le
  have hmar := margin hq0 hq1 ht0 ht
  have hKβ : (1 + kapA p) * (p.α * (1 + 4 * aE p * η)) ^ 2 * p.β ≤ 1 - mA p := by
    have e : (1 + kapA p) * (p.α * (1 + 4 * aE p * η)) ^ 2 * p.β =
        (1 + (1 - qA p) / (4 * qA p)) * qA p * (1 + 4 * aE p * η) ^ 2 := by
      unfold kapA qA; ring
    rw [e]; unfold mA
    have : (1 - 4 * aE p * η) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hv : Bdd (fun y => Cd p * η * (1 + C1 p) * |r y 1 - w y 1|) :=
    ((bdd_abs hg1).lin (bdd_abs hg1) (Cd p * η * (1 + C1 p)) 0).congr fun y => by ring
  have hD := bwd_sq' T hβ0 hβ1 hk hm hKβ hg4 hv hk'
    (fun y => D_rel T hp hFw hFr haη hbη hb y) hx
  have e : (fun y => (Cd p * η * (1 + C1 p) * |r y 1 - w y 1|) ^ 2) =
      fun y => (Cd p * (1 + C1 p)) ^ 2 * η ^ 2 * (r y 1 - w y 1) ^ 2 := by
    funext y; rw [mul_pow, sq_abs]; ring
  rw [e, S_smul T hβ (bdd_sq hg1)] at hD
  have hQ' : (1 + 1 / kapA p) / mA p = QA p := rfl
  rw [hQ'] at hD
  calc _ ≤ _ := hD
    _ = _ := by ring

/-! ## The node remainder in terms of output and inflation -/

/-- Woodford (2003), App. E (**AM–GM**): `cuv ≤ du² + ev²` when `d > 0` and `c² ≤ 4de`. -/
theorem amgm {c d e u v : ℝ} (hd : 0 < d) (hde : c ^ 2 ≤ 4 * d * e) :
    c * u * v ≤ d * u ^ 2 + e * v ^ 2 := by
  have h : 0 ≤ 4 * d * (d * u ^ 2 + e * v ^ 2 - c * u * v) := by
    have : 4 * d * (d * u ^ 2 + e * v ^ 2 - c * u * v) =
        (2 * d * u - c * v) ^ 2 + (4 * d * e - c ^ 2) * v ^ 2 := by ring
    rw [this]
    have : 0 ≤ (4 * d * e - c ^ 2) * v ^ 2 := mul_nonneg (by linarith) (sq_nonneg v)
    exact add_nonneg (sq_nonneg _) this
  have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 4 * d)).1 h
  linarith

/-- Woodford (2003), Ch. 7: `|x̂| ≤ |K̂| + |F̂|`, since `1 + ωθ ≥ 1`. -/
theorem abs_xr_le {p : Par} (hp : p.Std) (v : Fin 9 → ℝ) : |xr p v| ≤ |v 3| + |v 2| := by
  have hc : 1 ≤ p.c0 := by
    change 1 ≤ 1 + p.ω * p.θ
    nlinarith [hp.ω_nonneg, hp.one_lt_θ]
  unfold xr
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < p.c0), div_le_iff₀ (by linarith)]
  have := abs_sub (v 3) (v 2)
  have : 0 ≤ |v 3| + |v 2| := by positivity
  nlinarith

/-- Woodford (2003), Ch. 7: the reset gap is linear in the plan. -/
theorem xr_sub (p : Par) (u v : Fin 9 → ℝ) : xr p u - xr p v = xr p (u - v) := by
  unfold xr; simp only [Pi.sub_apply]; ring

/-- Woodford (2003), Ch. 7: the size of a direction, with `K̂ = F̂ + (1+ωθ)x̂` and
`|x̂| ≤ C|π|`: `‖h‖² ≤ ŷ² + (1 + 2c₀²C²)π² + 3F̂² + Δ̂² + Δ̂₋₁²`. -/
theorem nrm_le {p : Par} (hp : p.Std) {C : ℝ} (h : Fin 9 → ℝ) (hDp : ℝ)
    (hx : |xr p h| ≤ C * |h 1|) :
    nrm h hDp ≤ h 0 ^ 2 + (1 + 2 * p.c0 ^ 2 * C ^ 2) * h 1 ^ 2 + 3 * h 2 ^ 2 + h 4 ^ 2 +
      hDp ^ 2 := by
  have hc := hp.c0_pos
  have e3 : h 3 = h 2 + p.c0 * xr p h := by unfold xr; field_simp; ring
  have hx2 : xr p h ^ 2 ≤ C ^ 2 * h 1 ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hx 2
    rwa [sq_abs, mul_pow, sq_abs] at this
  have h3 : h 3 ^ 2 ≤ 2 * h 2 ^ 2 + 2 * p.c0 ^ 2 * (C ^ 2 * h 1 ^ 2) := by
    rw [e3]
    have := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 2 * p.c0 ^ 2)
    nlinarith [sq_nonneg (h 2 - p.c0 * xr p h)]
  unfold nrm
  linarith

/-- **Woodford (2003), §2.2 and App. E (the node remainder is negative in `(ŷ, π)` up to the
other directions).** If `R ≤ H0/2 + Kη‖h‖²` and `|x̂| ≤ C|π|`, then
`R ≤ (−A(σ+ω)/4 + Kη)ŷ² + (−λ̄₄ac₀α/4 + Kη(1 + 2c₀²C²))π² + 3KηF̂²
  + (A/(σ+ω) + Kη)Δ̂² + (λ̄₄αa/c₀ + Kη)Δ̂₋₁²`. -/
theorem R2_le {p : Par} (hp : p.Std) {A : ℝ} (hA : 0 < A) {K η R C : ℝ} (hK : 0 ≤ K)
    (hη : 0 ≤ η) (h : Fin 9 → ℝ) (hDp : ℝ) (hR : R ≤ H0 p A h hDp / 2 + K * η * nrm h hDp)
    (hx : |xr p h| ≤ C * |h 1|) :
    R ≤ (-(A * (p.σ + p.ω) / 4) + K * η) * h 0 ^ 2 +
      (-(lam4 p A * aE p * p.c0 * p.α / 4) + K * η * (1 + 2 * p.c0 ^ 2 * C ^ 2)) * h 1 ^ 2 +
      3 * K * η * h 2 ^ 2 + (A / (p.σ + p.ω) + K * η) * h 4 ^ 2 +
      (lam4 p A * p.α * aE p / p.c0 + K * η) * hDp ^ 2 := by
  have hc := hp.c0_pos
  have hα := hp.α_pos
  have hσω : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hl4 : 0 < lam4 p A := by
    unfold lam4
    have : 0 < 1 - p.α * p.β := by linarith [hp.ab_lt_one]
    have : 0 < 1 + p.ω := by linarith [hp.ω_nonneg]
    positivity
  have ha : 0 < aE p := by unfold aE; nlinarith [hp.one_lt_θ, hp.ω_nonneg]
  have hH := H0_le hp hA h hDp
  have m1 := amgm (c := A) (d := A * (p.σ + p.ω) / 4) (e := A / (p.σ + p.ω)) (u := |h 0|)
    (v := |h 4|) (by positivity) (le_of_eq (by field_simp))
  have m2 := amgm (c := lam4 p A * p.α * aE p) (d := lam4 p A * aE p * p.c0 * p.α / 4)
    (e := lam4 p A * p.α * aE p / p.c0) (u := |h 1|) (v := |hDp|) (by positivity)
    (le_of_eq (by field_simp))
  rw [sq_abs, sq_abs] at m1 m2
  have hn := nrm_le hp h hDp hx
  have hKn := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ K * η)
  linarith

/-- Woodford (2003), App. E (**the final estimate**, pure arithmetic): the bounds on the welfare
gap SR, on the norm SN and on the `F̂` and dispersion gaps combine into SR ≤ −(μ/C₈)SN. -/
theorem final_alg {S0 S1 S2 S4 SR SN a0 a1 K η D0 D1 E G0 G1 β C5 μ : ℝ} (hS0 : 0 ≤ S0)
    (hS1 : 0 ≤ S1) (hS4 : 0 ≤ S4) (hK : 0 ≤ K) (hη : 0 ≤ η) (hD0 : 0 ≤ D0) (hD1 : 0 ≤ D1)
    (hE : 0 ≤ E) (hG0 : 0 ≤ G0) (hG1 : 0 ≤ G1) (hβ1 : β ≤ 1) (hC5 : 0 ≤ C5)
    (hμ : 0 < μ) (hμ0 : μ ≤ a0 / 2) (hμ1 : μ ≤ a1 / 2)
    (hSR : SR ≤ (-a0 + K * η) * S0 + (-a1 + K * η * C5) * S1 + 3 * K * η * S2 +
      (G0 + K * η) * S4 + (G1 + K * η) * (β * S4))
    (hSN : SN ≤ S0 + C5 * S1 + 3 * S2 + S4 + β * S4) (h2 : S2 ≤ D0 * S0 + D1 * S1)
    (h4 : S4 ≤ E * η ^ 2 * S1) (hKη : K * η ≤ 1) (hη1 : η ≤ 1)
    (hZ : η * (K * (1 + 3 * D0) + K * (C5 + 3 * D1) + (G0 + G1 + 2) * E) ≤ μ) :
    SR ≤ -(μ / (1 + 3 * D0 + C5 + 3 * D1 + 2 * E)) * SN := by
  have t1 : 3 * K * η * S2 ≤ 3 * K * η * (D0 * S0 + D1 * S1) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have hηη : η ^ 2 ≤ η := by
    have := mul_le_mul_of_nonneg_right hη1 hη
    rw [one_mul] at this
    rw [sq]; exact this
  have h4' : S4 ≤ E * η * S1 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hηη hE) hS1
    linarith
  have h4'' : S4 ≤ E * S1 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hη1 hE) hS1
    linarith
  have t2 : (G0 + K * η) * S4 + (G1 + K * η) * (β * S4) ≤ (G0 + G1 + 2) * S4 := by
    have h' : (G1 + K * η) * β ≤ G1 + 1 := by
      have : (G1 + K * η) * β ≤ (G1 + K * η) * 1 :=
        mul_le_mul_of_nonneg_left hβ1 (by positivity)
      linarith
    have a1 : (G1 + K * η) * (β * S4) ≤ (G1 + 1) * S4 := by
      calc (G1 + K * η) * (β * S4) = ((G1 + K * η) * β) * S4 := by ring
        _ ≤ (G1 + 1) * S4 := mul_le_mul_of_nonneg_right h' hS4
    have a2 : (G0 + K * η) * S4 ≤ (G0 + 1) * S4 := mul_le_mul_of_nonneg_right (by linarith) hS4
    linarith
  have t3 : (G0 + G1 + 2) * S4 ≤ (G0 + G1 + 2) * (E * η * S1) :=
    mul_le_mul_of_nonneg_left h4' (by positivity)
  have p1 : 0 ≤ η * (K * (C5 + 3 * D1)) := by positivity
  have p2 : 0 ≤ η * ((G0 + G1 + 2) * E) := by positivity
  have p3 : 0 ≤ η * (K * (1 + 3 * D0)) := by positivity
  have c0 : -a0 + K * η * (1 + 3 * D0) ≤ -μ := by linarith
  have c1 : -a1 + η * (K * (C5 + 3 * D1) + (G0 + G1 + 2) * E) ≤ -μ := by linarith
  have s0 := mul_le_mul_of_nonneg_right c0 hS0
  have s1 := mul_le_mul_of_nonneg_right c1 hS1
  have hR : SR ≤ -μ * S0 + -μ * S1 := by linarith
  have hbS : β * S4 ≤ S4 := mul_le_of_le_one_left hS4 hβ1
  have q1 : 0 ≤ D0 * S1 := by positivity
  have q2 : 0 ≤ D1 * S0 := by positivity
  have q3 : 0 ≤ C5 * S0 := by positivity
  have q4 : 0 ≤ E * S0 := by positivity
  have hN : SN ≤ (1 + 3 * D0 + C5 + 3 * D1 + 2 * E) * (S0 + S1) := by linarith
  have hC : 0 < 1 + 3 * D0 + C5 + 3 * D1 + 2 * E := by positivity
  have : μ / (1 + 3 * D0 + C5 + 3 * D1 + 2 * E) * SN ≤ μ * (S0 + S1) := by
    calc _ ≤ μ / (1 + 3 * D0 + C5 + 3 * D1 + 2 * E) *
          ((1 + 3 * D0 + C5 + 3 * D1 + 2 * E) * (S0 + S1)) :=
          mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by field_simp
  linarith

/-! ## Strict local maximality -/

/-- Woodford (2003), Ch. 3, (2.20): along two feasible plans near the steady state, the reset-gap
difference is controlled by the inflation difference, `|x̂_r − x̂_w| ≤ C₁|π_r − π_w|`. -/
theorem xr_gap {p : Par} (hp : p.Std) {e : Y → Fin 5 → ℝ} {w r : Y → Fin 9 → ℝ} {Dm1 : ℝ}
    (hFw : Feas T p e Dm1 w) (hFr : Feas T p e Dm1 r) {η : ℝ} (hbη : (p.θ - 1) * η ≤ 1 / 10)
    {y : Y} (h1 : |w y 1| ≤ η) (h2 : |xr p (w y)| ≤ η) (h3 : |r y 1 - w y 1| ≤ η)
    (h4 : |xr p (r y) - xr p (w y)| ≤ η) :
    |xr p (r y) - xr p (w y)| ≤ C1 p * |r y 1 - w y 1| := by
  have hb0 : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have hr7 : p.α * (Real.exp ((p.θ - 1) * (w y 1 + (r y 1 - w y 1))) - 1) +
      (1 - p.α) * (Real.exp (-((p.θ - 1) * (xr p (w y) + (xr p (r y) - xr p (w y))))) - 1) = 0 := by
    rw [show w y 1 + (r y 1 - w y 1) = r y 1 by ring,
      show xr p (w y) + (xr p (r y) - xr p (w y)) = xr p (r y) by ring]
    exact (hFr y).2.2.1
  exact price_gap hp.α_pos hp.α_lt_one hb0 hbη h1 h2 h3 h4 (hFw y).2.2.1 hr7

/-- **Woodford (2003), Ch. 6, §2.2 and §5, Ch. 7, App. E (the nonlinear date-0 Ramsey plan is a
strict local maximum of welfare, quantitatively).** For the efficient-frame economy `R0 A`
(`A > 0`) there are `δ > 0` and `c > 0` such that: if the bounded date-0 Ramsey plan `w`
(`RamseyL` with root lag `lagD0 Δ₋₁`, bounded disturbances `e`) is within `ε ≤ δ` of the efficient
steady state at every node (`Near`), then every bounded feasible plan `r` within `ρ ≤ δ` of `w` in
`(ŷ, π, F̂, K̂, Δ)` at every node satisfies, at every root `x₀`,
`W(r)(x₀) ≤ W(w)(x₀) − c·S[‖r − w‖²](x₀)`. -/
theorem local_max {p : Par} (hp : p.Std) {A : ℝ} (hA : 0 < A) :
    ∃ δ > 0, ∃ c > 0, ∀ {V : Type*} (T : LagTree V) (e : V → Fin 5 → ℝ) (w r : V → Fin 9 → ℝ)
      (Dm1 ε ρ : ℝ),
      VBdd e → VBdd w → VBdd r → RamseyL T p (R0 A) e (lagD0 Dm1) w → Feas T p e Dm1 r →
      0 ≤ ε → ε ≤ δ → 0 ≤ ρ → ρ ≤ δ →
      (∀ y, Near p A ε (e y) (lag0 T (fun z => w z 5) y) (lag0 T (fun z => w z 6) y) (w y)
        (lagDv T Dm1 w y)) →
      (∀ y, |r y 0 - w y 0| ≤ ρ ∧ |r y 1 - w y 1| ≤ ρ ∧ |r y 2 - w y 2| ≤ ρ ∧
        |r y 3 - w y 3| ≤ ρ ∧ |r y 4 - w y 4| ≤ ρ) →
      ∀ x, T.depth x = 0 → W T p A e r x ≤ W T p A e w x -
        c * S T p.β (fun y => nrm (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y)) x := by
  obtain ⟨δ₀, hδ₀, K, hK, hR2⟩ := R2_bound hp hA
  obtain ⟨hq0, hq1⟩ := qA_bounds hp
  obtain ⟨-, -, hQ, hC1, hCd⟩ := consts_pos hp
  have hβ0 := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hβ : |p.β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hα := hp.α_pos
  have hθ1 := hp.one_lt_θ
  have hσ := hp.σ_pos
  have hω := hp.ω_nonneg
  have hc := hp.c0_pos
  have hσω : 0 < p.σ + p.ω := by linarith
  have hl4 : 0 < lam4 p A := by
    unfold lam4
    have : 0 < 1 - p.α * p.β := by linarith [hp.ab_lt_one]
    have : 0 < 1 + p.ω := by linarith
    positivity
  have ha : 0 < aE p := by unfold aE; nlinarith
  -- the constants
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℝ, a0 = A * (p.σ + p.ω) / 4 := ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℝ, a1 = lam4 p A * aE p * p.c0 * p.α / 4 := ⟨_, rfl⟩
  obtain ⟨C5, hC5⟩ : ∃ C5 : ℝ, C5 = 1 + 2 * p.c0 ^ 2 * C1 p ^ 2 := ⟨_, rfl⟩
  obtain ⟨D0, hD0⟩ : ∃ D0 : ℝ, D0 = QA p * (72 * (1 - p.σ) ^ 2) := ⟨_, rfl⟩
  obtain ⟨D1, hD1⟩ : ∃ D1 : ℝ, D1 = QA p * (8 * p.α ^ 2 * p.β * (p.θ - 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = QA p * (Cd p * (1 + C1 p)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0 : ℝ, G0 = A / (p.σ + p.ω) := ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ, G1 = lam4 p A * p.α * aE p / p.c0 := ⟨_, rfl⟩
  have pa0 : 0 < a0 := by rw [ha0]; positivity
  have pa1 : 0 < a1 := by rw [ha1]; positivity
  have pC5 : 0 ≤ C5 := by rw [hC5]; positivity
  have pD0 : 0 ≤ D0 := by rw [hD0]; positivity
  have pD1 : 0 ≤ D1 := by rw [hD1]; positivity
  have pE : 0 ≤ E := by rw [hE]; positivity
  have pG0 : 0 ≤ G0 := by rw [hG0]; positivity
  have pG1 : 0 ≤ G1 := by rw [hG1]; positivity
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = K * (1 + 3 * D0) + K * (C5 + 3 * D1) + (G0 + G1 + 2) * E :=
    ⟨_, rfl⟩
  have pZ : 0 ≤ Z := by rw [hZ]; positivity
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = min a0 a1 / 2 := ⟨_, rfl⟩
  have pμ : 0 < μ := by rw [hμ]; exact half_pos (lt_min pa0 pa1)
  have hμ0 : μ ≤ a0 / 2 := by rw [hμ]; linarith [min_le_left a0 a1]
  have hμ1 : μ ≤ a1 / 2 := by rw [hμ]; linarith [min_le_right a0 a1]
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1 + aE p + p.θ + |1 - p.σ| + p.σ + K + Z := ⟨_, rfl⟩
  have hσ1 := abs_nonneg (1 - p.σ)
  have pB : 1 ≤ B := by rw [hB]; linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min ((1 - qA p) / (80 * B)) (μ / (Z + 1)) := ⟨_, rfl⟩
  have pd : 0 < d := by
    rw [hd]; exact lt_min (div_pos (by linarith) (by linarith)) (div_pos pμ (by linarith))
  have pC8 : 0 < 1 + 3 * D0 + C5 + 3 * D1 + 2 * E := by positivity
  refine ⟨min δ₀ (d / 4), lt_min hδ₀ (by linarith), μ / (1 + 3 * D0 + C5 + 3 * D1 + 2 * E),
    div_pos pμ pC8, ?_⟩
  intro V T e w r Dm1 ε ρ he hw hr hR hF hε0 hεδ hρ0 hρδ hN hS x hx
  have hεδ₀ : ε ≤ δ₀ := hεδ.trans (min_le_left _ _)
  have hρδ₀ : ρ ≤ δ₀ := hρδ.trans (min_le_left _ _)
  have hεd : ε ≤ d / 4 := hεδ.trans (min_le_right _ _)
  have hρd : ρ ≤ d / 4 := hρδ.trans (min_le_right _ _)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 2 * (ε + ρ) := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  have hεη : ε ≤ η := by rw [hη]; linarith
  have hρη : ρ ≤ η := by rw [hη]; linarith
  have hερη : ε + ρ ≤ η := by rw [hη]; linarith
  have hηd : η ≤ d := by rw [hη]; linarith
  have hηB : B * η ≤ (1 - qA p) / 80 := by
    have h1 : η ≤ (1 - qA p) / (80 * B) := hηd.trans (by rw [hd]; exact min_le_left _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  have hηZ : (Z + 1) * η ≤ μ := by
    have h1 : η ≤ μ / (Z + 1) := hηd.trans (by rw [hd]; exact min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  have hle : ∀ {X : ℝ}, X ≤ B → X * η ≤ B * η := fun h => mul_le_mul_of_nonneg_right h hη0
  have hB80 : B * η ≤ 1 / 80 := by linarith
  have haη : aE p * η ≤ 1 / 10 := by
    have := hle (X := aE p) (by rw [hB]; linarith); linarith
  have hθη' := hle (X := p.θ) (by rw [hB]; linarith)
  have hbη : (p.θ - 1) * η ≤ 1 / 10 := by linarith
  have hθη : p.θ * η ≤ 1 / 40 := by linarith
  have hU : (|1 - p.σ| + p.σ + 1) * η ≤ 1 := by
    have := hle (X := |1 - p.σ| + p.σ + 1) (by rw [hB]; linarith); linarith
  have ht5 : 5 * p.θ * η ≤ (1 - qA p) / 8 := by linarith
  have ht4 : 4 * aE p * η ≤ (1 - qA p) / 8 := by
    have := hle (X := aE p) (by rw [hB]; linarith); linarith
  have hKη : K * η ≤ 1 := by
    have := hle (X := K) (by rw [hB]; linarith); linarith
  have hη1 : η ≤ 1 := by
    have := hle (X := 1) pB; linarith
  -- the date-0 plan is feasible
  have hFw : Feas T p e Dm1 w := by
    have := feas_of_ramsey T p (R0 A) e (lagD0 Dm1) w hR
    simpa [lagD0] using this
  -- node bounds
  have hxw : ∀ y, |xr p (w y)| ≤ η := fun y => by
    obtain ⟨-, -, -, hw2, hw3, -⟩ := hN y
    have := abs_xr_le hp (w y); linarith
  have hxh : ∀ y, |xr p (r y) - xr p (w y)| ≤ η := fun y => by
    obtain ⟨-, -, h2, h3, -⟩ := hS y
    rw [xr_sub]
    have := abs_xr_le hp (r y - w y)
    simp only [Pi.sub_apply] at this
    linarith
  have hbF : ∀ y, |e y 1| ≤ η ∧ |e y 2| ≤ η ∧ |w y 0| ≤ η ∧ |w y 1| ≤ η ∧ |w y 2| ≤ η ∧
      |r y 0 - w y 0| ≤ η ∧ |r y 1 - w y 1| ≤ η ∧ |r y 2 - w y 2| ≤ η := fun y => by
    obtain ⟨he', hw0, hw1, hw2, -⟩ := hN y
    obtain ⟨h0, h1, h2, -⟩ := hS y
    exact ⟨(he' 1).trans hεη, (he' 2).trans hεη, hw0.trans hεη, hw1.trans hεη, hw2.trans hεη,
      h0.trans hρη, h1.trans hρη, h2.trans hρη⟩
  have hbD : ∀ y, |w y 1| ≤ η ∧ |xr p (w y)| ≤ η ∧ |r y 1 - w y 1| ≤ η ∧
      |xr p (r y) - xr p (w y)| ≤ η ∧ |lagDv T Dm1 w y - 1| ≤ η := fun y => by
    obtain ⟨-, -, hw1, -, -, -, -, -, -, -, hDp, -⟩ := hN y
    exact ⟨hw1.trans hεη, hxw y, (hS y).2.1.trans hρη, hxh y, hDp.trans hεη⟩
  have gF := gap_F T hp hw hr hFw hF hθη hU ht5 hbF x
  have gD := gap_D T hp hw hr hFw hF haη hbη ht4 hbD hx
  -- the reset gap of the direction
  have hx' : ∀ y, |xr p (r y - w y)| ≤ C1 p * |(r y - w y) 1| := fun y => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hbD y
    rw [← xr_sub, Pi.sub_apply]
    exact xr_gap T hp hFw hF hbη h1 h2 h3 h4
  -- bounded node functions
  have hg : ∀ i, Bdd (fun y => r y i - w y i) := bdd_gap hw hr
  have hgl : Bdd (lag0 T (fun z => r z 4 - w z 4)) := (hg 4).lag T
  obtain ⟨Bw, hBw⟩ := hw
  obtain ⟨Br, hBr⟩ := hr
  have hBh : ∀ y i, |(r y - w y) i| ≤ Br + Bw := fun y i => by
    rw [Pi.sub_apply]; exact (abs_sub _ _).trans (add_le_add (hBr y i) (hBw y i))
  obtain ⟨Bl, hBl⟩ := hgl
  have hpair : ∀ y, ‖(r y - w y, lag0 T (fun z => r z 4 - w z 4) y)‖ ≤ |Br + Bw| + |Bl| :=
    fun y => by
      rw [Prod.norm_def]
      have := norm_le_of_vbdd hBh y
      have h2 : ‖lag0 T (fun z => r z 4 - w z 4) y‖ ≤ |Bl| := by
        rw [Real.norm_eq_abs]; exact (hBl y).trans (le_abs_self _)
      exact max_le (by linarith [abs_nonneg Bl]) (by linarith [abs_nonneg (Br + Bw)])
  have hnb : Bdd (fun y => nrm (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y)) :=
    (bdd_of_cont (F := fun q : (Fin 9 → ℝ) × ℝ => nrm q.1 q.2) (by unfold nrm; fun_prop)
      hpair).congr fun y => rfl
  have hHb : Bdd (fun y => H0 p A (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y)) :=
    (bdd_of_cont (F := fun q : (Fin 9 → ℝ) × ℝ => H0 p A q.1 q.2) (by unfold H0 xr; fun_prop)
      hpair).congr fun y => rfl
  -- the node remainder
  have hsm : ∀ y, TidyR6aHess.Small ρ (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y) := fun y => by
    obtain ⟨h0, h1, h2, h3, h4⟩ := hS y
    simp only [TidyR6aHess.Small, Pi.sub_apply]
    exact ⟨h0, h1, h2, h3, h4, abs_lag0_le T hρ0 (fun z => (hS z).2.2.2.2) y⟩
  have hR2y := fun y => hR2 (e y) _ _ (w y) (lagDv T Dm1 w y) (r y - w y)
    (lag0 T (fun z => r z 4 - w z 4) y) ε ρ hε0 hρ0 hεδ₀ hρδ₀ (hN y) (hsm y)
  have hnn : ∀ y, 0 ≤ nrm (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y) := fun y => by
    unfold nrm; positivity
  obtain ⟨BH, hBH⟩ := hHb
  obtain ⟨Bn, hBn⟩ := hnb
  have hRb : Bdd (fun y => R2 p A (e y) (lag0 T (fun z => w z 5) y) (lag0 T (fun z => w z 6) y)
      (w y) (lagDv T Dm1 w y) (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y)) := by
    refine ⟨BH / 2 + K * (ε + ρ) * Bn, fun y => ?_⟩
    have h1 := hR2y y
    have h2 := hBH y
    have h3 : nrm (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y) ≤ Bn :=
      (le_abs_self _).trans (hBn y)
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ K * (ε + ρ))
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith
  -- pointwise: the remainder and the norm in terms of the five squares
  have ptR : ∀ y, R2 p A (e y) (lag0 T (fun z => w z 5) y) (lag0 T (fun z => w z 6) y)
      (w y) (lagDv T Dm1 w y) (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y) ≤
      (-a0 + K * η) * (r y 0 - w y 0) ^ 2 + (-a1 + K * η * C5) * (r y 1 - w y 1) ^ 2 +
        3 * K * η * (r y 2 - w y 2) ^ 2 + (G0 + K * η) * (r y 4 - w y 4) ^ 2 +
        (G1 + K * η) * (lag0 T (fun z => r z 4 - w z 4) y) ^ 2 := fun y => by
    have h1 := (abs_le.1 (hR2y y)).2
    have h2 := mul_le_mul_of_nonneg_left hερη hK
    have h3 := mul_le_mul_of_nonneg_right h2 (hnn y)
    have := R2_le hp hA hK hη0 (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y)
      (R := R2 p A (e y) (lag0 T (fun z => w z 5) y) (lag0 T (fun z => w z 6) y)
        (w y) (lagDv T Dm1 w y) (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y))
      (by linarith) (hx' y)
    simp only [Pi.sub_apply] at this
    rw [ha0, ha1, hC5, hG0, hG1]
    linarith
  have ptN : ∀ y, nrm (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y) ≤
      1 * (r y 0 - w y 0) ^ 2 + C5 * (r y 1 - w y 1) ^ 2 + 3 * (r y 2 - w y 2) ^ 2 +
        1 * (r y 4 - w y 4) ^ 2 + 1 * (lag0 T (fun z => r z 4 - w z 4) y) ^ 2 := fun y => by
    have := nrm_le hp (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y) (hx' y)
    simp only [Pi.sub_apply] at this
    rw [hC5]
    linarith
  have hb4 : Bdd (fun y => (lag0 T (fun z => r z 4 - w z 4) y) ^ 2) := bdd_sq ((hg 4).lag T)
  have hcomb := fun c0 c1 c2 c3 c4 => S_comb5 T hβ (bdd_sq (hg 0)) (bdd_sq (hg 1))
    (bdd_sq (hg 2)) (bdd_sq (hg 4)) hb4 c0 c1 c2 c3 c4 x
  have hlag : S T p.β (fun y => (lag0 T (fun z => r z 4 - w z 4) y) ^ 2) x =
      p.β * S T p.β (fun y => (r y 4 - w y 4) ^ 2) x := by
    have e1 : (fun y => (lag0 T (fun z => r z 4 - w z 4) y) ^ 2) =
        lag0 T (fun z => (r z 4 - w z 4) ^ 2) := by
      funext y; unfold lag0; split_ifs <;> simp
    rw [e1, S_lag_root T hβ (bdd_sq (hg 4)) hx]
  have bnd := fun (c0 c1 c2 c3 c4 : ℝ) => (((((bdd_sq (hg 0)).lin (bdd_sq (hg 1)) c0 c1).lin
    (bdd_sq (hg 2)) 1 c2).lin (bdd_sq (hg 4)) 1 c3).lin hb4 1 c4)
  have hSR := S_mono T hβ0.le hβ1 hRb ((bnd (-a0 + K * η) (-a1 + K * η * C5) (3 * K * η)
    (G0 + K * η) (G1 + K * η)).congr fun y => by ring) ptR x
  rw [hcomb, hlag] at hSR
  have hSN := S_mono T hβ0.le hβ1 ⟨Bn, hBn⟩ ((bnd 1 C5 3 1 1).congr fun y => by ring) ptN x
  rw [hcomb, hlag] at hSN
  simp only [one_mul] at hSN
  have hWd := welfare_diff T hp A he ⟨Bw, hBw⟩ ⟨Br, hBr⟩ hR hF hx
  have hS0 := S_nonneg T hβ0.le hβ1 (bdd_sq (hg 0)) (fun y => sq_nonneg _) x
  have hS1 := S_nonneg T hβ0.le hβ1 (bdd_sq (hg 1)) (fun y => sq_nonneg _) x
  have hS4 := S_nonneg T hβ0.le hβ1 (bdd_sq (hg 4)) (fun y => sq_nonneg _) x
  have h2 : S T p.β (fun y => (r y 2 - w y 2) ^ 2) x ≤
      D0 * S T p.β (fun y => (r y 0 - w y 0) ^ 2) x +
        D1 * S T p.β (fun y => (r y 1 - w y 1) ^ 2) x := by
    rw [hD0, hD1]; linarith
  have h4 : S T p.β (fun y => (r y 4 - w y 4) ^ 2) x ≤
      E * η ^ 2 * S T p.β (fun y => (r y 1 - w y 1) ^ 2) x := by
    rw [hE]; exact gD
  have hZ' : η * (K * (1 + 3 * D0) + K * (C5 + 3 * D1) + (G0 + G1 + 2) * E) ≤ μ := by
    rw [← hZ]; linarith
  have fin := final_alg hS0 hS1 hS4 hK hη0 pD0 pD1 pE pG0 pG1 hβ1.le pC5 pμ hμ0 hμ1
    hSR hSN h2 h4 hKη hη1 hZ'
  linarith

/-! ## The date-0 plan of the efficient economy -/

/-- **Woodford (2003), Ch. 7 (the date-0 plan of the efficient economy is near the steady
state).** For `A > 0` and every `ε > 0` there is `δₑ > 0` such that on every event tree, for
disturbances `‖e‖ ≤ δₑ` and initial dispersion `|Δ₋₁ − 1| ≤ δₑ`, the date-0 Ramsey conditions of
`R0 A` have a solution within `ε` of the efficient steady state at every node. -/
theorem date0_near {p : Par} (hp : p.Std) {A : ℝ} (hA : 0 < A) {ε : ℝ} (hε : 0 < ε) :
    ∃ δe > 0, ∀ {Z : Type*} (T : LagTree Z) (e : Z → Fin 5 → ℝ) (Dm1 : ℝ),
      (∀ y, ‖e y‖ ≤ δe) → |Dm1 - 1| ≤ δe →
        ∃ w : Z → Fin 9 → ℝ, RamseyL T p (R0 A) e (lagD0 Dm1) w ∧
          ∀ y, ‖w y - ramseySS p (R0 A)‖ ≤ ε := by
  have hG : (R0 A).Au * Gw p (R0 A) ≠ 0 := by
    have : 0 < Gw p (R0 A) := by
      simp only [Gw, R0, zero_mul, add_zero]; linarith [hp.σ_pos, hp.ω_nonneg]
    exact mul_ne_zero hA.ne' this.ne'
  obtain ⟨r, hr, δN, hδN, C, hC, hNw⟩ := ramsey_newton (R0 A) hp hG
  obtain ⟨δc, hδc, hsmall⟩ := phiR_zero_small (R0 A) hp (τ := ε / C) (by positivity)
  refine ⟨min δN δc, lt_min hδN hδc, fun {Z} T e Dm1 he hD => ?_⟩
  have hd : ∀ y : Z, ‖(fun _ => d0R p (R0 A) Dm1) y‖ ≤ min δN δc := fun _ => by
    have := norm_d0R p (R0 A) Dm1
    rw [(lam_R0 p A).1, abs_zero, add_zero] at this
    exact this.trans hD
  obtain ⟨z, ⟨-, hz0⟩, -, hzest⟩ := hNw T e (fun _ => d0R p (R0 A) Dm1)
    (fun y => (he y).trans (min_le_left _ _)) (fun y => (hd y).trans (min_le_left _ _))
  have hres := hsmall T e (fun _ => d0R p (R0 A) Dm1) (fun y => (he y).trans (min_le_right _ _))
    (fun y => (hd y).trans (min_le_right _ _))
  refine ⟨fun y => z y + ramseySS p (R0 A), ?_, fun y => ?_⟩
  · rw [date0_iffR]
    have e1 : (fun y => z y + ramseySS p (R0 A) - ramseySS p (R0 A)) = z := by
      funext y; abel
    rw [e1]; exact hz0
  · have := hzest (fun _ => 0) (fun _ => by rw [norm_zero]; exact hr.le) (ε / C) (by positivity)
      hres y
    rw [sub_zero] at this
    have e2 : z y + ramseySS p (R0 A) - ramseySS p (R0 A) = z y := by abel
    rw [e2]
    calc _ ≤ _ := this
      _ = ε := by field_simp

/-- **Woodford (2003), Ch. 6, §2.2 and §5, Ch. 7 (the nonlinear date-0 Ramsey plan is a strict
local maximum of welfare).** For the efficient-frame economy `R0 A` with `A > 0` there are
`δ, c, δₑ > 0` such that on every event tree, for disturbances `‖e‖ ≤ δₑ` and initial dispersion
`|Δ₋₁ − 1| ≤ δₑ`, the date-0 Ramsey conditions have a bounded solution `w` with: every bounded
feasible plan `r` within `δ` of `w` in `(ŷ, π, F̂, K̂, Δ)` at every node satisfies, at every
root, `W(r) ≤ W(w) − c·S[‖r − w‖²]`. -/
theorem date0_strict_max {p : Par} (hp : p.Std) {A : ℝ} (hA : 0 < A) :
    ∃ δ > 0, ∃ c > 0, ∃ δe > 0, ∀ {Z : Type*} (T : LagTree Z) (e : Z → Fin 5 → ℝ) (Dm1 : ℝ),
      (∀ y, ‖e y‖ ≤ δe) → |Dm1 - 1| ≤ δe →
        ∃ w : Z → Fin 9 → ℝ, RamseyL T p (R0 A) e (lagD0 Dm1) w ∧ VBdd w ∧
          ∀ r : Z → Fin 9 → ℝ, VBdd r → Feas T p e Dm1 r →
            (∀ y, |r y 0 - w y 0| ≤ δ ∧ |r y 1 - w y 1| ≤ δ ∧ |r y 2 - w y 2| ≤ δ ∧
              |r y 3 - w y 3| ≤ δ ∧ |r y 4 - w y 4| ≤ δ) →
            ∀ x, T.depth x = 0 → W T p A e r x ≤ W T p A e w x -
              c * S T p.β (fun y => nrm (r y - w y) (lag0 T (fun z => r z 4 - w z 4) y)) x := by
  obtain ⟨δ, hδ, c, hc, hLM⟩ := local_max hp hA
  obtain ⟨δe, hδe, hnear⟩ := date0_near hp hA hδ
  refine ⟨δ, hδ, c, hc, min δe δ, lt_min hδe hδ, fun {Z} T e Dm1 he hD => ?_⟩
  obtain ⟨w, hR, hw⟩ := hnear T e Dm1 (fun y => (he y).trans (min_le_left _ _))
    (hD.trans (min_le_left _ _))
  have hcw : ∀ y (i : Fin 9), |w y i - ramseySS p (R0 A) i| ≤ δ := fun y i => by
    have := norm_le_pi_norm (w y - ramseySS p (R0 A)) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at this
    exact this.trans (hw y)
  have hce : ∀ y (i : Fin 5), |e y i| ≤ δ := fun y i => by
    have := norm_le_pi_norm (e y) i
    rw [Real.norm_eq_abs] at this
    exact this.trans ((he y).trans (min_le_right _ _))
  have l0 := (lam_R0 p A).1
  have l1 := (lam_R0 p A).2
  have l3 := (lam_eq p A).1
  have l2 := (lam_eq p A).2
  have hss : ramseySS p (R0 A) = ![0, 0, 0, 0, 1, 0, 0, lam3 p A, lam4 p A] := by
    funext i; fin_cases i <;> simp [ramseySS, l0, l1, l2, l3]
  have s : ∀ y, |w y 0| ≤ δ ∧ |w y 1| ≤ δ ∧ |w y 2| ≤ δ ∧ |w y 3| ≤ δ ∧ |w y 4 - 1| ≤ δ ∧
      |w y 5| ≤ δ ∧ |w y 6| ≤ δ ∧ |w y 7 - lam3 p A| ≤ δ ∧ |w y 8 - lam4 p A| ≤ δ := fun y => by
    have h := hcw y
    rw [hss] at h
    exact ⟨by simpa using h 0, by simpa using h 1, by simpa using h 2, by simpa using h 3,
      by simpa using h 4, by simpa using h 5, by simpa using h 6, by simpa using h 7,
      by simpa using h 8⟩
  have hwb : VBdd w := ⟨δ + ‖ramseySS p (R0 A)‖, fun y i => by
    have := norm_le_pi_norm (ramseySS p (R0 A)) i
    rw [Real.norm_eq_abs] at this
    have := abs_add_le (w y i - ramseySS p (R0 A) i) (ramseySS p (R0 A) i)
    rw [sub_add_cancel] at this
    linarith [hcw y i]⟩
  have heb : VBdd e := ⟨δ, hce⟩
  refine ⟨w, hR, hwb, fun r hr hF hS x hx => hLM T e w r Dm1 δ δ heb hwb hr hR hF hδ.le le_rfl
    hδ.le le_rfl (fun y => ?_) hS x hx⟩
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8⟩ := s y
  refine ⟨hce y, s0, s1, s2, s3, s4, s5, s6, s7, s8, ?_, ?_, ?_⟩
  · unfold lagDv; split_ifs
    · exact hD.trans (min_le_right _ _)
    · exact (s (T.par y)).2.2.2.2.1
  · unfold lag0; split_ifs
    · rw [abs_zero]; exact hδ.le
    · exact (s (T.par y)).2.2.2.2.2.1
  · unfold lag0; split_ifs
    · rw [abs_zero]; exact hδ.le
    · exact (s (T.par y)).2.2.2.2.2.2.1

end Woodford.StabilizationWelfare.TidyR6aLocalMax
