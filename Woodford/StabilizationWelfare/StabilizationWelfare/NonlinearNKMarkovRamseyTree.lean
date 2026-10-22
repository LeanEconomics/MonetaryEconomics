/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyLin
import StabilizationWelfare.NonlinearNKMarkovGeneral

/-!
# The linearised Ramsey operator with a lag on an event tree: inverse and a-priori bound

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (optimal commitment from a timeless
perspective: predetermined `Δ_{−1}, λ_{−1}`) and Appendix A.3 (the sequence-space implicit
function theorem).

The Ramsey conditions contain the LAGGED variables `Δ_{t−1}, λ₁_{t−1}, λ₂_{t−1}`. They are posed on
an event tree (`LagTree`): a state space with a Markov operator `M` (the conditional expectation
of next-period values), a parent map `par` (the previous node) and a depth (the date), with
`M(f ∘ par) = f` (the parent of every successor is the current node) and `M` blind to root
nodes. The event tree of a finite Markov chain is an instance (`chainTree` in
`NonlinearNKMarkovRamseyIFT`).

* `lag0` (the lag, `0` at the roots), `bwd` (the backward solution of `g = c·lag g + f`, explicit
  as a finite sum), `fwdS` (the forward solution of `g = cMg + f`), with bounds and uniqueness.
* `LR`: the linearised Ramsey operator `v ↦ DQr(v₋, v) + DNr(Mv)` with zero initial lag.
* `LinvR`: its inverse, built by the reduction of `NonlinearNKMarkovRamseyLin` (dispersion and
  summed multiplier backward with root `α`, output by the factorisation
  `βMy − (1+β+κθ)y + lag y = (βM − βz₂)(1 − z₁ lag)y` with `0 < z₁ < 1 < z₂`, the remaining
  variables forward with root `αβ` or algebraically).
* **`LR_LinvR`** (`L(L⁻¹r) = r`), **`LR_inj`** (a bounded solution of `Lv = 0` is `0`),
  **`LinvR_LR`**, **`LinvR_bound`** (`‖L⁻¹r‖ ≤ K‖r‖` with `K` depending only on the
  parameters): the a-priori bound with predetermined variables, uniformly over event trees.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyTree

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin

/-- Woodford (2003), Ch. 7 and App. A.3 (**an event tree**): nodes `X`, the conditional
expectation of next-period values `M` (a Markov operator), the parent node `par` and the date
`depth`; the parent of every successor is the current node (`M(f ∘ par) = f`) and successors are
never roots. -/
structure LagTree (X : Type*) where
  /-- The expectation of next-period values. -/
  M : (X → ℝ) →ₗ[ℝ] (X → ℝ)
  /-- `M` is a Markov operator. -/
  markov : IsMarkov M
  /-- The previous node. -/
  par : X → X
  /-- The date of a node. -/
  depth : X → ℕ
  /-- The parent of a non-root node is one date earlier. -/
  depth_par : ∀ x, depth x ≠ 0 → depth (par x) + 1 = depth x
  /-- The parent of every successor is the current node. -/
  M_par : ∀ f : X → ℝ, M (fun x => f (par x)) = f
  /-- Successors are never roots. -/
  M_root : ∀ f g : X → ℝ, (∀ x, depth x ≠ 0 → f x = g x) → M f = M g

variable {X : Type*} (T : LagTree X)

/-! ## Lags, backward and forward solutions -/

/-- Woodford (2003), Ch. 7: the lagged value, `0` at the roots (zero initial deviation). -/
def lag0 (f : X → ℝ) (x : X) : ℝ := if T.depth x = 0 then 0 else f (T.par x)

/-- The expectation of the lag is the current value. -/
theorem M_lag0 (f : X → ℝ) : T.M (lag0 T f) = f := by
  rw [T.M_root (lag0 T f) (fun x => f (T.par x)) fun x hx => by simp [lag0, hx]]
  exact T.M_par f

/-- The lag is linear. -/
theorem lag0_lin (c d : ℝ) (f g : X → ℝ) (x : X) :
    lag0 T (fun y => c * f y + d * g y) x = c * lag0 T f x + d * lag0 T g x := by
  unfold lag0; split_ifs <;> simp

/-- The lag keeps bounds. -/
theorem abs_lag0_le {f : X → ℝ} {A : ℝ} (hA : 0 ≤ A) (hf : ∀ x, |f x| ≤ A) (x : X) :
    |lag0 T f x| ≤ A := by
  unfold lag0; split_ifs
  · simpa using hA
  · exact hf _

/-- Woodford (2003), Ch. 7 (**the backward solution**): `bwd c f x = ∑_{j ≤ date} cʲ f(parʲ x)`
solves `g = c·lag g + f` with zero initial value. -/
noncomputable def bwd (c : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  ∑ j ∈ Finset.range (T.depth x + 1), c ^ j * f (T.par^[j] x)

/-- The backward recursion. -/
theorem bwd_eq (c : ℝ) (f : X → ℝ) (x : X) : bwd T c f x = c * lag0 T (bwd T c f) x + f x := by
  unfold lag0
  split_ifs with h
  · simp [bwd, h]
  · obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero h
    have hp := T.depth_par x h
    rw [hd] at hp
    have hpd : T.depth (T.par x) = d := by omega
    unfold bwd
    rw [hd, hpd, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, one_mul, Function.iterate_zero, id]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Function.iterate_succ_apply, pow_succ]
    ring

/-- The backward solution is bounded: `|bwd c f| ≤ A/(1 − c)` for `0 ≤ c < 1`, `|f| ≤ A`. -/
theorem abs_bwd_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {f : X → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A) (x : X) : |bwd T c f x| ≤ A / (1 - c) := by
  unfold bwd
  calc _ ≤ ∑ j ∈ Finset.range (T.depth x + 1), c ^ j * A := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (pow_nonneg hc0 j)]
        exact mul_le_mul_of_nonneg_left (hf _) (pow_nonneg hc0 j)
    _ = A * ∑ j ∈ Finset.range (T.depth x + 1), c ^ j := by rw [Finset.mul_sum]; ring_nf
    _ ≤ A * (1 - c)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        rw [← tsum_geometric_of_lt_one hc0 hc1]
        exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hc0 j)
          (summable_geometric_of_lt_one hc0 hc1)
    _ = A / (1 - c) := by ring

/-- Woodford (2003), App. A.3: the backward recursion has a unique solution (induction on the
date): if `g = c·lag g` then `g = 0`. -/
theorem zero_of_eq_lag {c : ℝ} {g : X → ℝ} (h : ∀ x, g x = c * lag0 T g x) (x : X) : g x = 0 := by
  suffices H : ∀ n, ∀ x, T.depth x = n → g x = 0 from H _ x rfl
  intro n
  induction n with
  | zero => intro x hx; rw [h x]; simp [lag0, hx]
  | succ n ih =>
    intro x hx
    have hp := T.depth_par x (by omega)
    rw [h x]; simp only [lag0, (show T.depth x ≠ 0 by omega), ↓reduceIte]
    rw [ih _ (by omega), mul_zero]

/-- The expectation operator is linear in two-term combinations. -/
theorem M_lin (a b : ℝ) (f g : X → ℝ) :
    T.M (fun x => a * f x + b * g x) = fun x => a * T.M f x + b * T.M g x := by
  have e : (fun x => a * f x + b * g x) = a • f + b • g := rfl
  rw [e, map_add, map_smul, map_smul]; rfl

/-- The expectation of a constant. -/
theorem M_const (c : ℝ) : T.M (fun _ => c) = fun _ => c := by
  have e : (fun _ : X => c) = c • fun _ => (1 : ℝ) := by funext; simp
  rw [e, map_smul, T.markov.1]

/-- Woodford (2003), App. A.3: a bounded solution of `g = cMg` with `|c| < 1` is `0`. -/
theorem zero_of_eq_cM {c : ℝ} (hc : |c| < 1) {g : X → ℝ} {A : ℝ} (hA : ∀ x, |g x| ≤ A)
    (h : ∀ x, g x = c * T.M g x) (x : X) : g x = 0 := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA x)
  have hn : ∀ n : ℕ, ∀ x, |g x| ≤ |c| ^ n * A := by
    intro n
    induction n with
    | zero => intro x; simpa using hA x
    | succ n ih =>
      intro x
      rw [h x, abs_mul, pow_succ, mul_comm (|c| ^ n) |c|, mul_assoc]
      exact mul_le_mul_of_nonneg_left (T.markov.2 g _ ih x) (abs_nonneg c)
  have ht : Tendsto (fun n : ℕ => |c| ^ n * A) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg c) hc).mul_const A
  exact abs_nonpos_iff.1 (ge_of_tendsto' ht fun n => hn n x)

/-- Woodford (2003), (A.13) for a scalar (**the forward solution**): `g = ∑ cᵏMᵏf`. -/
noncomputable def fwdS (c : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  fwdSol !![c] T.M (fun y => ![f y]) x 0

/-- The summed size of the powers of `(c)`. -/
noncomputable def Sg (c : ℝ) : ℝ := ∑' k, mnorm (!![c] ^ k)

/-- `Sg c ≥ 0`. -/
theorem Sg_nonneg (c : ℝ) : 0 ≤ Sg c := tsum_nonneg fun _ => mnorm_nonneg _

/-- `∑ mnorm((c)ᵏ) < ∞` for `|c| < 1`. -/
theorem summable_c {c : ℝ} (hc : |c| < 1) : Summable fun k => mnorm (!![c] ^ k) :=
  summable_mnorm_pow_of_lt (by simpa [mnorm] using hc)

/-- Woodford (2003), (A.13): the forward solution solves `g = cMg + f` and `|g| ≤ Sg(c)·A`. -/
theorem fwdS_spec {c : ℝ} (hc : |c| < 1) {f : X → ℝ} {A : ℝ} (hA0 : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A) :
    (∀ x, |fwdS T c f x| ≤ Sg c * A) ∧ ∀ x, fwdS T c f x = c * T.M (fwdS T c f) x + f x := by
  have hb : ∀ x, ‖(![f x] : Fin 1 → ℝ)‖ ≤ A := fun x =>
    (pi_norm_le_iff_of_nonneg hA0).2 fun i => by fin_cases i; simpa using hf x
  obtain ⟨h1, h2⟩ := fwdSol_spec (summable_c hc) T.markov hA0 hb
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := (norm_le_pi_norm (fwdSol !![c] T.M (fun y => ![f y]) x) 0).trans (h1 x)
    rwa [Real.norm_eq_abs] at this
  · have := congrFun (h2 x) 0
    simp only [Fin.isValue, Matrix.cons_mulVec, dotProduct, Finset.univ_unique,
      Fin.default_eq_zero, Matrix.cons_val_fin_one, Mv, Finset.sum_singleton, Matrix.empty_mulVec,
      Pi.add_apply] at this
    exact this

/-- Woodford (2003), App. A.3: a bounded solution of `g = cMg + f` is the forward solution. -/
theorem fwdS_unique {c : ℝ} (hc : |c| < 1) {f g : X → ℝ} {A B : ℝ} (hA0 : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A) (hg : ∀ x, |g x| ≤ B) (h : ∀ x, g x = c * T.M g x + f x) (x : X) :
    g x = fwdS T c f x := by
  obtain ⟨h1, h2⟩ := fwdS_spec T hc hA0 hf
  have hz := zero_of_eq_cM T hc (g := fun y => g y - fwdS T c f y) (A := B + Sg c * A)
    (fun y => (abs_sub _ _).trans (add_le_add (hg y) (h1 y))) (fun y => by
      have e := M_lin T 1 (-1) g (fwdS T c f)
      have e' : (fun y => g y - fwdS T c f y) = fun y => 1 * g y + -1 * fwdS T c f y := by
        funext; ring
      rw [e', e, h y, h2 y]; ring) x
  linarith

/-- Woodford (2003), Ch. 7: the stable root `z₁` of `βz² − (1+β+κθ)z + 1`. -/
noncomputable def z1 (p : Par) : ℝ :=
  ((1 + p.β + p.κ * p.θ) - Real.sqrt ((1 + p.β + p.κ * p.θ) ^ 2 - 4 * p.β)) / (2 * p.β)

/-- Woodford (2003), Ch. 7: the unstable root `z₂` of `βz² − (1+β+κθ)z + 1`. -/
noncomputable def z2 (p : Par) : ℝ :=
  ((1 + p.β + p.κ * p.θ) + Real.sqrt ((1 + p.β + p.κ * p.θ) ^ 2 - 4 * p.β)) / (2 * p.β)

/-- Woodford (2003), Ch. 7 (**the root condition**): `0 < z₁ < 1 < z₂`, `βz₁z₂ = 1`,
`β(z₁ + z₂) = 1 + β + κθ`. -/
theorem z_props {p : Par} (hp : p.Std) :
    0 < z1 p ∧ z1 p < 1 ∧ 1 < z2 p ∧ p.β * z1 p * z2 p = 1 ∧
      p.β * (z1 p + z2 p) = 1 + p.β + p.κ * p.θ := by
  have hβ0 := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hc : 0 < p.κ * p.θ := mul_pos hp.κ_pos (by linarith [hp.one_lt_θ])
  unfold z1 z2
  set c := p.κ * p.θ
  set A := 1 + p.β + c with hA
  set D := A ^ 2 - 4 * p.β with hD
  have hDpos : (1 - p.β + c) ^ 2 < D := by rw [hD, hA]; nlinarith
  have hD0 : 0 < D := lt_of_le_of_lt (sq_nonneg _) hDpos
  set q := Real.sqrt D with hq
  have hqq : q * q = D := Real.mul_self_sqrt hD0.le
  have hq1 : 1 - p.β + c < q := by rw [hq]; exact Real.lt_sqrt_of_sq_lt hDpos
  have hqA : q < A := by
    rw [hq, Real.sqrt_lt' (by linarith)]; rw [hD]; nlinarith
  refine ⟨by apply div_pos <;> linarith, by rw [div_lt_one (by linarith)]; linarith,
    by rw [one_lt_div (by linarith)]; linarith, by field_simp; nlinarith, by field_simp; ring⟩

/-! ## The linearised operator and its inverse -/

/-- Woodford (2003), Ch. 7: the lagged vector, `0` at the roots. -/
def lagv {n : ℕ} (v : X → Fin n → ℝ) (x : X) : Fin n → ℝ := fun i => lag0 T (fun y => v y i) x

/-- Woodford (2003), Ch. 7 and App. A.3 (**the linearised Ramsey operator with a lag**):
`(Lv)(x) = DQr(v(par x), v(x)) + DNr((Mv)(x))`, zero lag at the roots. -/
noncomputable def LR (p : Par) (R : RPar) (v : X → Fin 9 → ℝ) (x : X) : Fin 9 → ℝ :=
  DQr p R (lagv T v x) (v x) + DNr p R (Mv T.M v x)

/-- The inverse, dispersion: `Δ̂ = αΔ̂₋ + (a/b)r₇ + r₈` (`red_D`). -/
noncomputable def Dv (p : Par) (r : X → Fin 9 → ℝ) : X → ℝ :=
  bwd T p.α (fun x => aE p / (p.θ - 1) * r x 7 + r x 8)

/-- The inverse, summed multiplier: `μ = αμ₋ + r₂ + r₃ − (λ̄₁c₀/b)r₇` (`red_mu`). -/
noncomputable def Muv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) : X → ℝ :=
  bwd T p.α (fun x => r x 2 + r x 3 - ramseyLam p R 0 * p.c0 / (p.θ - 1) * r x 7)

/-- The inverse, NKPC forcing (`red_pc`). -/
noncomputable def gv (p : Par) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (1 - p.α) / (p.c0 * p.α) * (r x 6 - r x 5) +
    (r x 7 - p.α * p.β * T.M (fun y => r y 7) x) / (p.α * (p.θ - 1))

/-- The inverse, targeting-rule forcing times `A_uG` (`red_target`). -/
noncomputable def Ftv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (1 - p.α * p.β) * (p.σ + p.ω) * (-((1 - p.α) * aE p / p.c0 *
    (lag0 T (Muv T p R r) x + ramseyLam p R 3 * lag0 T (Dv T p r) x)) -
    (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1) * r x 7 + r x 2 -
    (1 - p.α) / (p.α * p.c0) * r x 1) - (r x 0 - lag0 T (fun y => r y 0) x) -
  (1 - R.Φ) * R.Au * (Dv T p r x - lag0 T (Dv T p r) x) -
  (1 - p.α * p.β) * (1 + p.ω) * (Muv T p R r x - lag0 T (Muv T p R r) x)

/-- The inverse, targeting-rule forcing `f = F/(A_uG)`: `ŷ − ŷ₋ + θπ = f`. -/
noncomputable def fv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  Ftv T p R r x / (R.Au * Gw p R)

/-- The inverse, forcing of `βMy − (1+β+κθ)y + lag y = h`. -/
noncomputable def hv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  p.θ * gv T p r x + p.β * T.M (fv T p R r) x - fv T p R r x

/-- The inverse, the forward factor `u = y − z₁ lag y`. -/
noncomputable def uv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (1 / z2 p) (fun x => -hv T p R r x / (p.β * z2 p))

/-- The inverse, output: `y = z₁ lag y + u`. -/
noncomputable def yv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) : X → ℝ :=
  bwd T (z1 p) (uv T p R r)

/-- The inverse, inflation from the targeting rule: `π = (f − y + lag y)/θ`. -/
noncomputable def piv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (fv T p R r x - yv T p R r x + lag0 T (yv T p R r) x) / p.θ

/-- The inverse, `F̂` forward with root `αβ`. -/
noncomputable def Fv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (p.α * p.β) (fun x => (1 - p.α * p.β) * (1 - p.σ) * yv T p R r x +
    p.α * p.β * (p.θ - 1) * T.M (piv T p R r) x + r x 5)

/-- The inverse, the relative price `x̂` from the price index. -/
noncomputable def xv (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (p.α * (p.θ - 1) * piv T p R r x - r x 7) / ((1 - p.α) * (p.θ - 1))

/-- The inverse, `λ̂₁` from the output condition (`red_l1`). -/
noncomputable def l1v (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (r x 0 + R.Au * Gw p R * yv T p R r x + (1 - R.Φ) * R.Au * Dv T p r x +
    (1 - p.α * p.β) * (1 + p.ω) * Muv T p R r x) / ((1 - p.α * p.β) * (p.σ + p.ω))

/-- The inverse, `λ̂₄` forward with root `αβ`. -/
noncomputable def l4v (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (p.α * p.β) (fun x => (1 - R.Φ) * R.Au * yv T p R r x +
    p.α * p.β * ramseyLam p R 3 * aE p * T.M (piv T p R r) x + r x 4)

/-- The inverse, `λ̂₃` from the `F̂` condition. -/
noncomputable def l3v (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (r x 2 - (l1v T p R r x + ramseyLam p R 0 * Fv T p R r x - p.α * (lag0 T (l1v T p R r) x +
    ramseyLam p R 0 * ((p.θ - 1) * piv T p R r x + Fv T p R r x))) +
    (1 - p.α) * (aE p / p.c0) * (l4v T p R r x - ramseyLam p R 3 * aE p * xv T p R r x)) /
      ((1 - p.α) * ((p.θ - 1) / p.c0)) + ramseyLam p R 2 * (p.θ - 1) * xv T p R r x

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse of the linearised Ramsey operator**). -/
noncomputable def LinvR (p : Par) (R : RPar) (r : X → Fin 9 → ℝ) (x : X) : Fin 9 → ℝ :=
  ![yv T p R r x, piv T p R r x, Fv T p R r x, Fv T p R r x + p.c0 * xv T p R r x,
    Dv T p r x, l1v T p R r x, Muv T p R r x - l1v T p R r x, l3v T p R r x, l4v T p R r x]

/-! ## Uniform bounds -/

/-- Two-term bounds. -/
theorem lb2 {f g : X → ℝ} {cf cg A : ℝ} (hf : ∀ x, |f x| ≤ cf * A) (hg : ∀ x, |g x| ≤ cg * A)
    (k1 k2 : ℝ) (x : X) : |k1 * f x + k2 * g x| ≤ (|k1| * cf + |k2| * cg) * A := by
  have h1 := mul_le_mul_of_nonneg_left (hf x) (abs_nonneg k1)
  have h2 := mul_le_mul_of_nonneg_left (hg x) (abs_nonneg k2)
  calc _ ≤ |k1 * f x| + |k2 * g x| := abs_add_le _ _
    _ = |k1| * |f x| + |k2| * |g x| := by rw [abs_mul, abs_mul]
    _ ≤ _ := by nlinarith

/-- The expectation keeps scaled bounds. -/
theorem lbM {f : X → ℝ} {c A : ℝ} (hf : ∀ x, |f x| ≤ c * A) (x : X) : |T.M f x| ≤ c * A :=
  T.markov.2 f _ hf x

/-- The lag keeps scaled bounds. -/
theorem lbLag {f : X → ℝ} {c A : ℝ} (h0 : 0 ≤ c * A) (hf : ∀ x, |f x| ≤ c * A) (x : X) :
    |lag0 T f x| ≤ c * A :=
  abs_lag0_le T h0 hf x

/-- Woodford (2003), App. A.3: a bound on the dispersion part of the inverse, uniform over event
trees. -/
theorem bd_Dv {p : Par} (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) → ∀ y, |Dv T p r y| ≤ c * A := by
  have h1 : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  refine ⟨(|aE p / (p.θ - 1)| * 1 + |1| * 1) / (1 - p.α), by positivity,
    fun T r A hA hr y => ?_⟩
  have hin := lb2 (f := fun y => r y 7) (g := fun y => r y 8) (cf := 1) (cg := 1) (A := A)
    (fun y => by simpa using hr y 7) (fun y => by simpa using hr y 8) (aE p / (p.θ - 1)) 1
  have hb := abs_bwd_le T hp.α_pos.le hp.α_lt_one
    (A := (|aE p / (p.θ - 1)| * 1 + |1| * 1) * A) (by positivity)
    (fun y => by simpa only [one_mul] using hin y) y
  exact hb.trans (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a bound on the summed-multiplier part of the inverse. -/
theorem bd_Muv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |Muv T p R r y| ≤ c * A := by
  have h1 : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  set k := ramseyLam p R 0 * p.c0 / (p.θ - 1)
  refine ⟨(|1| * (|1| * 1 + |1| * 1) + |-k| * 1) / (1 - p.α), by positivity,
    fun T r A hA hr y => ?_⟩
  have h23 := lb2 (f := fun y => r y 2) (g := fun y => r y 3) (cf := 1) (cg := 1) (A := A)
    (fun y => by simpa using hr y 2) (fun y => by simpa using hr y 3) 1 1
  have hin := lb2 (f := fun y => 1 * r y 2 + 1 * r y 3) (g := fun y => r y 7) (cg := 1) (A := A)
    h23 (fun y => by simpa using hr y 7) 1 (-k)
  have hb := abs_bwd_le T hp.α_pos.le hp.α_lt_one
    (A := (|1| * (|1| * 1 + |1| * 1) + |-k| * 1) * A) (by positivity)
    (f := fun x => r x 2 + r x 3 - k * r x 7) (fun y => by
      have := hin y
      simp only [one_mul] at this
      convert this using 2; ring) y
  exact hb.trans (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a bound on the NKPC forcing. -/
theorem bd_gv {p : Par} : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) → ∀ y, |gv T p r y| ≤ c * A := by
  set k1 := (1 - p.α) / (p.c0 * p.α)
  set k2 := 1 / (p.α * (p.θ - 1))
  refine ⟨|k1| * (|1| * 1 + |-1| * 1) + |k2| * (|1| * 1 + |-(p.α * p.β)| * 1), by positivity,
    fun T r A hA hr y => ?_⟩
  have h65 := lb2 (f := fun y => r y 6) (g := fun y => r y 5) (cf := 1) (cg := 1) (A := A)
    (fun y => by simpa using hr y 6) (fun y => by simpa using hr y 5) 1 (-1)
  have h77 := lb2 (f := fun y => r y 7) (g := T.M fun y => r y 7) (cf := 1) (cg := 1) (A := A)
    (fun y => by simpa using hr y 7) (lbM T fun y => by simpa using hr y 7) 1 (-(p.α * p.β))
  have := lb2 h65 h77 k1 k2 y
  convert this using 2
  simp only [gv, k1, k2]; ring

/-- Woodford (2003), App. A.3: a bound on the targeting-rule forcing. -/
theorem bd_fv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |fv T p R r y| ≤ c * A := by
  obtain ⟨cD, hcD, hD⟩ := bd_Dv hp
  obtain ⟨cM, hcM, hM⟩ := bd_Muv R hp
  set s := (1 - p.α * p.β) * (p.σ + p.ω)
  set k0 := (1 - p.α) * aE p / p.c0
  set k7 := (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1)
  set k1 := (1 - p.α) / (p.α * p.c0)
  set Av := (1 - R.Φ) * R.Au
  set s2 := (1 - p.α * p.β) * (1 + p.ω)
  set c1 := |-k0| * (|1| * cM + |ramseyLam p R 3| * cD) + |-k7| * 1
  set c2 := |1| * c1 + |1| * (|1| * 1 + |-k1| * 1)
  set c3 := |1| * (|1| * 1 + |-1| * 1) + |Av| * (|1| * cD + |-1| * cD)
  set c4 := |s| * c2 + |-1| * (c3 + |s2| * (|1| * cM + |-1| * cM))
  refine ⟨|1 / (R.Au * Gw p R)| * c4, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ k y, |r y k| ≤ 1 * A := fun k y => by simpa using hr y k
  have hDl := lbLag T (by positivity) (hD T r A hA hr)
  have hMl := lbLag T (by positivity) (hM T r A hA hr)
  have e1 := lb2 (lb2 (A := A) hMl hDl 1 (ramseyLam p R 3)) (hr' 7) (-k0) (-k7)
  have e2 := lb2 (f := fun y => -k0 * (1 * lag0 T (Muv T p R r) y + ramseyLam p R 3 *
    lag0 T (Dv T p r) y) + -k7 * r y 7) e1 (lb2 (hr' 2) (hr' 1) 1 (-k1)) 1 1
  have e3 := lb2 (f := fun y => r y 0) (g := lag0 T fun y => r y 0) (hr' 0)
    (lbLag T (by positivity) (hr' 0)) 1 (-1)
  have e4 := lb2 (f := fun y => 1 * r y 0 + -1 * lag0 T (fun y => r y 0) y)
    (g := fun y => 1 * Dv T p r y + -1 * lag0 T (Dv T p r) y) e3
    (lb2 (hD T r A hA hr) hDl 1 (-1)) 1 Av
  have e5 := lb2 (f := fun y => 1 * (1 * r y 0 + -1 * lag0 T (fun y => r y 0) y) +
    Av * (1 * Dv T p r y + -1 * lag0 T (Dv T p r) y))
    (g := fun y => 1 * Muv T p R r y + -1 * lag0 T (Muv T p R r) y) e4
    (lb2 (hM T r A hA hr) hMl 1 (-1)) 1 s2
  have e6 := lb2 (f := fun y => 1 * (-k0 * (1 * lag0 T (Muv T p R r) y + ramseyLam p R 3 *
    lag0 T (Dv T p r) y) + -k7 * r y 7) + 1 * (1 * r y 2 + -k1 * r y 1))
    (g := fun y => 1 * (1 * (1 * r y 0 + -1 * lag0 T (fun y => r y 0) y) +
      Av * (1 * Dv T p r y + -1 * lag0 T (Dv T p r) y)) +
        s2 * (1 * Muv T p R r y + -1 * lag0 T (Muv T p R r) y)) e2 e5 s (-1) y
  have e7 : |fv T p R r y| = |1 / (R.Au * Gw p R)| * |Ftv T p R r y| := by
    rw [fv, div_eq_mul_one_div, abs_mul, mul_comm]
  rw [e7, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  convert e6 using 2
  · simp only [Ftv, s, k0, k7, k1, Av, s2]; ring
  · simp only [c4, c2, c1, c3]; ring

/-- Woodford (2003), App. A.3: a bound on the forcing of the second-order output equation. -/
theorem bd_hv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |hv T p R r y| ≤ c * A := by
  obtain ⟨cg, hcg, hg⟩ := bd_gv (p := p)
  obtain ⟨cf, hcf, hf⟩ := bd_fv R hp
  refine ⟨|1| * (|p.θ| * cg + |p.β| * cf) + |-1| * cf, by positivity,
    fun T r A hA hr y => ?_⟩
  have := lb2 (lb2 (hg T r A hA hr) (lbM T (hf T r A hA hr)) p.θ p.β) (hf T r A hA hr) 1 (-1) y
  convert this using 2
  simp only [hv]; ring

/-- `|1/z₂| < 1`. -/
theorem abs_inv_z2 {p : Par} (hp : p.Std) : |1 / z2 p| < 1 := by
  obtain ⟨-, -, h2, -, -⟩ := z_props hp
  rw [abs_of_pos (by positivity), div_lt_one (by linarith)]; exact h2

/-- `|αβ| < 1`. -/
theorem abs_ab {p : Par} (hp : p.Std) : |p.α * p.β| < 1 := by
  rw [abs_of_pos hp.ab_pos]; exact hp.ab_lt_one

/-- Woodford (2003), App. A.3: a bound on the forward factor `u`, and its equation
`u = (1/z₂)Mu − h/(βz₂)`. -/
theorem bd_uv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |uv T p R r y| ≤ c * A) ∧ ∀ y, uv T p R r y =
        1 / z2 p * T.M (uv T p R r) y + -hv T p R r y / (p.β * z2 p) := by
  obtain ⟨ch, hch, hh⟩ := bd_hv R hp
  refine ⟨Sg (1 / z2 p) * (|-(1 / (p.β * z2 p))| * ch + |0| * 0), by
    have := Sg_nonneg (1 / z2 p); positivity, fun T r A hA hr => ?_⟩
  have hin := lb2 (g := fun _ => (0 : ℝ)) (cg := 0) (hh T r A hA hr) (fun _ => by simp)
    (-(1 / (p.β * z2 p))) 0
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_inv_z2 hp) (A := (|-(1 / (p.β * z2 p))| * ch + |0| * 0) * A)
    (by positivity) (f := fun y => -hv T p R r y / (p.β * z2 p)) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on output, `y = z₁ lag y + u`. -/
theorem bd_yv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |yv T p R r y| ≤ c * A := by
  obtain ⟨cu, hcu, hu⟩ := bd_uv R hp
  obtain ⟨hz0, hz1, -, -, -⟩ := z_props hp
  have h1 : 0 < 1 - z1 p := by linarith
  refine ⟨cu / (1 - z1 p), by positivity, fun T r A hA hr y => ?_⟩
  exact (abs_bwd_le T hz0.le hz1 (by positivity) (hu T r A hA hr).1 y).trans
    (le_of_eq (by ring))

/-- Woodford (2003), App. A.3: a bound on inflation. -/
theorem bd_piv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |piv T p R r y| ≤ c * A := by
  obtain ⟨cf, hcf, hf⟩ := bd_fv R hp
  obtain ⟨cy, hcy, hy⟩ := bd_yv R hp
  refine ⟨|1 / p.θ| * (|1| * (|1| * cf + |-1| * cy) + |1| * cy), by positivity,
    fun T r A hA hr y => ?_⟩
  have hY := hy T r A hA hr
  have := lb2 (lb2 (hf T r A hA hr) hY 1 (-1)) (lbLag T (by positivity) hY) 1 1
  have e := lb2 (g := fun _ => (0 : ℝ)) (cg := 0) this (fun _ => by simp) (1 / p.θ) 0 y
  convert e using 2
  · simp only [piv]; ring
  · ring

/-- Woodford (2003), App. A.3: a bound on `F̂`, and its forward equation. -/
theorem bd_Fv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |Fv T p R r y| ≤ c * A) ∧ ∀ y, Fv T p R r y = p.α * p.β * T.M (Fv T p R r) y +
        ((1 - p.α * p.β) * (1 - p.σ) * yv T p R r y +
          p.α * p.β * (p.θ - 1) * T.M (piv T p R r) y + r y 5) := by
  obtain ⟨cy, hcy, hy⟩ := bd_yv R hp
  obtain ⟨cπ, hcπ, hπ⟩ := bd_piv R hp
  set k1 := (1 - p.α * p.β) * (1 - p.σ)
  set k2 := p.α * p.β * (p.θ - 1)
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨Sg (p.α * p.β) * ci, by have := Sg_nonneg (p.α * p.β); positivity,
    fun T r A hA hr => ?_⟩
  have hin := lb2 (lb2 (hy T r A hA hr) (lbM T (hπ T r A hA hr)) k1 k2)
    (f := fun y => k1 * yv T p R r y + k2 * T.M (piv T p R r) y) (g := fun y => r y 5)
    (cg := 1) (fun y => by simpa using hr y 5) 1 1
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_ab hp) (A := ci * A) (by positivity)
    (f := fun y => k1 * yv T p R r y + k2 * T.M (piv T p R r) y + r y 5) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on `λ̂₄`, and its forward equation. -/
theorem bd_l4v {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |l4v T p R r y| ≤ c * A) ∧ ∀ y, l4v T p R r y = p.α * p.β * T.M (l4v T p R r) y +
        ((1 - R.Φ) * R.Au * yv T p R r y +
          p.α * p.β * ramseyLam p R 3 * aE p * T.M (piv T p R r) y + r y 4) := by
  obtain ⟨cy, hcy, hy⟩ := bd_yv R hp
  obtain ⟨cπ, hcπ, hπ⟩ := bd_piv R hp
  set k1 := (1 - R.Φ) * R.Au
  set k2 := p.α * p.β * ramseyLam p R 3 * aE p
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨Sg (p.α * p.β) * ci, by have := Sg_nonneg (p.α * p.β); positivity,
    fun T r A hA hr => ?_⟩
  have hin := lb2 (lb2 (hy T r A hA hr) (lbM T (hπ T r A hA hr)) k1 k2)
    (f := fun y => k1 * yv T p R r y + k2 * T.M (piv T p R r) y) (g := fun y => r y 4)
    (cg := 1) (fun y => by simpa using hr y 4) 1 1
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_ab hp) (A := ci * A) (by positivity)
    (f := fun y => k1 * yv T p R r y + k2 * T.M (piv T p R r) y + r y 4) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on the relative price `x̂`. -/
theorem bd_xv {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |xv T p R r y| ≤ c * A := by
  obtain ⟨cπ, hcπ, hπ⟩ := bd_piv R hp
  set k := 1 / ((1 - p.α) * (p.θ - 1))
  refine ⟨|k * (p.α * (p.θ - 1))| * cπ + |-k| * 1, by positivity, fun T r A hA hr y => ?_⟩
  have := lb2 (hπ T r A hA hr) (g := fun y => r y 7) (cg := 1)
    (fun y => by simpa using hr y 7) (k * (p.α * (p.θ - 1))) (-k) y
  convert this using 2
  simp only [xv, k]; ring

/-- Woodford (2003), App. A.3: a bound on `λ̂₁`. -/
theorem bd_l1v {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |l1v T p R r y| ≤ c * A := by
  obtain ⟨cy, hcy, hy⟩ := bd_yv R hp
  obtain ⟨cD, hcD, hD⟩ := bd_Dv hp
  obtain ⟨cM, hcM, hM⟩ := bd_Muv R hp
  set k := 1 / ((1 - p.α * p.β) * (p.σ + p.ω))
  set c1 := |k| * 1 + |k * (R.Au * Gw p R)| * cy
  set c2 := |k * ((1 - R.Φ) * R.Au)| * cD + |k * ((1 - p.α * p.β) * (1 + p.ω))| * cM
  refine ⟨|1| * c1 + |1| * c2, by positivity, fun T r A hA hr y => ?_⟩
  have e1 := lb2 (f := fun y => r y 0) (cf := 1) (fun y => by simpa using hr y 0)
    (hy T r A hA hr) k (k * (R.Au * Gw p R))
  have e2 := lb2 (hD T r A hA hr) (hM T r A hA hr) (k * ((1 - R.Φ) * R.Au))
    (k * ((1 - p.α * p.β) * (1 + p.ω)))
  have := lb2 e1 e2 1 1 y
  convert this using 2
  simp only [l1v, k]; ring

/-- Woodford (2003), App. A.3: a bound on `λ̂₃`. -/
theorem bd_l3v {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |l3v T p R r y| ≤ c * A := by
  obtain ⟨c1, hc1, h1⟩ := bd_l1v R hp
  obtain ⟨cF, hcF, hF⟩ := bd_Fv R hp
  obtain ⟨cπ, hcπ, hπ⟩ := bd_piv R hp
  obtain ⟨c4, hc4, h4⟩ := bd_l4v R hp
  obtain ⟨cx, hcx, hx⟩ := bd_xv R hp
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
  simp only [l3v, k, L0, ka, La, Lb]
  field_simp
  ring

/-! ## The inverse is a right inverse -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r`**): for every bounded forcing `r` on
every event tree, the constructed process solves the linearised Ramsey system. -/
theorem LR_LinvR {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    (r : X → Fin 9 → ℝ) (A : ℝ) (hA : 0 ≤ A) (hr : ∀ y k, |r y k| ≤ A) :
    LR T p R (LinvR T p R r) = r := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := z_props hp
  have hz2 : z2 p ≠ 0 := by linarith
  obtain ⟨_, _, hu⟩ := bd_uv R hp
  obtain ⟨_, _, hF⟩ := bd_Fv R hp
  obtain ⟨_, _, h4⟩ := bd_l4v R hp
  have Eu := (hu T r A hA hr).2
  have EF := (hF T r A hA hr).2
  have E4 := (h4 T r A hA hr).2
  set v := LinvR T p R r with hvdef
  set y := yv T p R r
  set π := piv T p R r
  set D := Dv T p r
  set μ := Muv T p R r
  set f := fv T p R r
  -- the scalar equations
  have ED : ∀ x, D x = p.α * lag0 T D x + (aE p / (p.θ - 1) * r x 7 + r x 8) := fun x =>
    bwd_eq T _ _ x
  have EM : ∀ x, μ x = p.α * lag0 T μ x +
      (r x 2 + r x 3 - ramseyLam p R 0 * p.c0 / (p.θ - 1) * r x 7) := fun x => bwd_eq T _ _ x
  have Ey : ∀ x, y x = z1 p * lag0 T y x + uv T p R r x := fun x => bwd_eq T _ _ x
  have E7 : ∀ x, p.α * (p.θ - 1) * π x - (1 - p.α) * (p.θ - 1) * xv T p R r x = r x 7 :=
    fun x => by simp only [xv, π]; field_simp; ring
  have Et : ∀ x, y x - lag0 T y x + p.θ * π x = f x := fun x => by
    simp only [π, piv]; field_simp; ring
  have EMy : ∀ x, T.M (uv T p R r) x = T.M y x - z1 p * y x := fun x => by
    have e : uv T p R r = fun x => 1 * y x + -z1 p * lag0 T y x := by
      funext x; rw [Ey x]; ring
    rw [e, M_lin, M_lag0]; ring
  have EMπ : ∀ x, T.M π x = (T.M f x - T.M y x + y x) / p.θ := fun x => by
    have e : π = fun x => (1 / p.θ) * (1 * f x + -1 * y x) + (1 / p.θ) * lag0 T y x := by
      funext x; simp only [π, piv]; ring
    rw [e, M_lin, M_lin, M_lag0]; field_simp; ring
  have Epc : ∀ x, π x = p.κ * y x + p.β * T.M π x + gv T p r x := fun x => by
    have h1 := Eu x
    have h2 := EMy x
    have hhv : hv T p R r x = p.θ * gv T p r x + p.β * T.M f x - f x := rfl
    have hux : uv T p R r x = y x - z1 p * lag0 T y x := by rw [Ey x]; ring
    rw [EMπ x]
    have ht := Et x
    have key : p.β * T.M y x - (1 + p.β + p.κ * p.θ) * y x + lag0 T y x = hv T p R r x := by
      rw [h2, hux] at h1
      linear_combination (norm := (field_simp; ring)) (-(p.β * z2 p)) * h1 + y x * hzs -
        lag0 T y x * hzz
    rw [hhv] at key
    linear_combination (norm := (field_simp; ring)) (1 / p.θ) * ht + (1 / p.θ) * key
  -- the component functions of `v`
  have v0 : (fun z => v z 0) = y := by funext z; simp [hvdef, LinvR, y]
  have v1 : (fun z => v z 1) = π := by funext z; simp [hvdef, LinvR, π]
  have v2 : (fun z => v z 2) = Fv T p R r := by funext z; simp [hvdef, LinvR]
  have v3 : (fun z => v z 3) = fun z => 1 * Fv T p R r z + p.c0 * xv T p R r z := by
    funext z; simp [hvdef, LinvR]
  have v4 : (fun z => v z 4) = D := by funext z; simp [hvdef, LinvR, D]
  have v5 : (fun z => v z 5) = l1v T p R r := by funext z; simp [hvdef, LinvR]
  have v6 : (fun z => v z 6) = fun z => 1 * μ z + -1 * l1v T p R r z := by
    funext z; simp [hvdef, LinvR, μ]; ring
  have v7 : (fun z => v z 7) = l3v T p R r := by funext z; simp [hvdef, LinvR]
  have v8 : (fun z => v z 8) = l4v T p R r := by funext z; simp [hvdef, LinvR]
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  have hvx : ∀ x k, v x k = (fun z => v z k) x := fun _ _ => rfl
  have E0 : ∀ x, -(R.Au * Gw p R * y x) - (1 - R.Φ) * R.Au * D x +
      (1 - p.α * p.β) * (p.σ + p.ω) * l1v T p R r x -
        (1 - p.α * p.β) * (1 + p.ω) * μ x = r x 0 := fun x => by
    simp only [l1v, y, D, μ]; field_simp; ring
  -- the nine components
  set Rr : X → Fin 9 → ℝ := fun x => DQr p R (lagv T v x) (v x) + DNr p R (Mv T.M v x) with hRr
  have c7 : ∀ x, Rr x 7 = r x 7 := fun x => by
    change (DQr p R (lagv T v x) (v x) + DNr p R (Mv T.M v x)) 7 = r x 7
    rw [red_x, hvx x 1, hvx x 2, hvx x 3, v1, v2, v3]
    simp only
    rw [← E7 x]; field_simp; ring
  have c8 : ∀ x, Rr x 8 = r x 8 := fun x => by
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl x 4, hvx x 1, hvx x 2, hvx x 3, hvx x 4, v1, v2, v3, v4]
    simp only
    linear_combination (norm := (field_simp; ring)) ED x - aE p / (p.θ - 1) * E7 x
  have c5 : ∀ x, Rr x 5 = r x 5 := fun x => by
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm x 1, hm x 2, hvx x 0, hvx x 2, v0, v1, v2]
    linear_combination EF x
  have c4 : ∀ x, Rr x 4 = r x 4 := fun x => by
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm x 1, hm x 8, hvx x 0, hvx x 8, v0, v1, v8]
    linear_combination E4 x
  have c0 : ∀ x, Rr x 0 = r x 0 := fun x => by
    change (DQr p R (lagv T v x) (v x) + DNr p R (Mv T.M v x)) 0 = r x 0
    rw [← red_l1 R hp, hvx x 0, hvx x 4, hvx x 5, hvx x 6, v0, v4, v5, v6]
    simp only
    linear_combination E0 x
  have c2 : ∀ x, Rr x 2 = r x 2 := fun x => by
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl x 5, hvx x 1, hvx x 2, hvx x 3, hvx x 5, hvx x 7, hvx x 8, v1, v2, v3, v5, v7, v8]
    simp only [l3v]
    field_simp
    ring
  have c3 : ∀ x, Rr x 3 = r x 3 := fun x => by
    have h := red_mu R hp (lagv T v x) (v x) (Mv T.M v x)
    rw [hl x 5, hl x 6, hvx x 5, hvx x 6, v5, v6, lag0_lin] at h
    simp only at h
    have h2 := c2 x
    have h7 := c7 x
    simp only [hRr] at h2 h7 ⊢
    rw [h2, h7] at h
    linear_combination (-1 : ℝ) * h + EM x
  have c6 : ∀ x, Rr x 6 = r x 6 := fun x => by
    have h := red_pc R hp (lagv T v x) (v x) (Mv T.M v x)
    have h5 := c5 x
    have h7 := c7 x
    simp only [hRr] at h5 h7 ⊢
    rw [h5, h7, hm x 1, hm x 2, hm x 3, hvx x 0, hvx x 1, v0, v1, v2, v3, M_lin] at h
    have hm7 : p.α * (p.θ - 1) * T.M π x - (1 - p.α) * (p.θ - 1) *
        ((1 * T.M (Fv T p R r) x + p.c0 * T.M (xv T p R r) x - T.M (Fv T p R r) x) / p.c0) =
          T.M (fun z => r z 7) x := by
      have e : (fun z => r z 7) = fun z => (p.α * (p.θ - 1)) * π z +
          (-(1 - p.α) * (p.θ - 1)) * xv T p R r z := by
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
    have h0m : -(R.Au * Gw p R * lagv T v x 0) - (1 - R.Φ) * R.Au * lagv T v x 4 +
        (1 - p.α * p.β) * (p.σ + p.ω) * lagv T v x 5 -
          (1 - p.α * p.β) * (1 + p.ω) * (lagv T v x 5 + lagv T v x 6) =
            lag0 T (fun z => r z 0) x := by
      simp only [lagv, lag0]
      split_ifs
      · ring
      · have := c0 (T.par x)
        change (DQr p R (lagv T v (T.par x)) (v (T.par x)) +
          DNr p R (Mv T.M v (T.par x))) 0 = r (T.par x) 0 at this
        rw [← red_l1 R hp] at this
        exact this
    have h := red_target R hp (lagv T v x) (v x) (Mv T.M v x) _ h0m
    have h2 := c2 x
    have h7 := c7 x
    have h0 := c0 x
    simp only [hRr] at h2 h7 h0 ⊢
    rw [h2, h7, h0, hl x 0, hl x 4, hl x 5, hl x 6, hvx x 0, hvx x 1, hvx x 4, hvx x 5,
      hvx x 6, v0, v1, v4, v5, v6, lag0_lin] at h
    simp only at h
    have ht := Et x
    have hF : R.Au * Gw p R * f x = Ftv T p R r x := by
      rw [show f x = Ftv T p R r x / (R.Au * Gw p R) from rfl, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hG
    simp only [Ftv] at hF
    have hk : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hab hωσ) (div_ne_zero h1α (mul_ne_zero hα hc0))
    have key : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) *
        (Rr x 1 - r x 1) = 0 := by
      simp only [hRr]
      linear_combination h - R.Au * Gw p R * ht - hF
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  funext x i
  fin_cases i
  exacts [c0 x, c1 x, c2 x, c3 x, c4 x, c5 x, c6 x, c7 x, c8 x]

/-- The lag of the zero function. -/
theorem lag0_zero (x : X) : lag0 T (fun _ => (0 : ℝ)) x = 0 := by unfold lag0; split_ifs <;> rfl

/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity: the a-priori bound with predetermined
variables**): on every event tree, a bounded solution of the homogeneous linearised Ramsey
system with zero initial lag is zero. -/
theorem LR_inj {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    (v : X → Fin 9 → ℝ) (B : ℝ) (hB : ∀ x k, |v x k| ≤ B) (h0 : LR T p R v = 0) : v = 0 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := z_props hp
  have hz2 : z2 p ≠ 0 := by linarith
  have hR : ∀ x, DQr p R (lagv T v x) (v x) + DNr p R (Mv T.M v x) = 0 := fun x =>
    congrFun h0 x
  have hRk : ∀ x k, (DQr p R (lagv T v x) (v x) + DNr p R (Mv T.M v x)) k = 0 := fun x k => by
    rw [hR x]; rfl
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  -- the predetermined block
  have hD : ∀ x, v x 4 = 0 := zero_of_eq_lag T (c := p.α) fun x => by
    have := red_D R hp (lagv T v x) (v x) (Mv T.M v x)
    rw [hRk, hRk, hl] at this; simpa using this
  have hμ : ∀ x, v x 5 + v x 6 = 0 := zero_of_eq_lag T (c := p.α) (g := fun z => v z 5 + v z 6)
    fun x => by
      have := red_mu R hp (lagv T v x) (v x) (Mv T.M v x)
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
    rw [← red_x R (lagv T v z) (v z) (Mv T.M v z)]
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
  have h0m : ∀ x, -(R.Au * Gw p R * lagv T v x 0) - (1 - R.Φ) * R.Au * lagv T v x 4 +
      (1 - p.α * p.β) * (p.σ + p.ω) * lagv T v x 5 -
        (1 - p.α * p.β) * (1 + p.ω) * (lagv T v x 5 + lagv T v x 6) = 0 := fun x => by
    simp only [lagv, lag0]
    split_ifs
    · ring
    · have := red_l1 R hp (lagv T v (T.par x)) (v (T.par x)) (Mv T.M v (T.par x))
      rw [hRk] at this; exact this
  have hcs := fun x => commitment_system R hp (lagv T v x) (v x) (Mv T.M v x) (hR x) (h0m x)
    (hm7 x)
  -- the commitment block
  set y : X → ℝ := fun z => v z 0 with hy
  set π : X → ℝ := fun z => v z 1 with hπ
  have Et : ∀ x, y x - lag0 T y x + p.θ * π x = 0 := fun x => by
    obtain ⟨-, -, -, h4⟩ := hcs x
    rw [hl, hl, hl, hl, hDf, lag0_zero] at h4
    have e := lag0_lin T 1 1 (fun z => v z 5) (fun z => v z 6) x
    simp only [one_mul] at e
    rw [← e, hμf, lag0_zero] at h4
    simp only [mul_zero, add_zero, sub_zero] at h4
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hG
    · linarith
  have Epc : ∀ x, π x = p.κ * y x + p.β * T.M π x := fun x => by
    obtain ⟨-, -, h3, -⟩ := hcs x
    rw [hm] at h3; exact h3
  have hyB : ∀ x, |y x| ≤ B := fun x => hB x 0
  have hπf : π = fun z => (-1 / p.θ) * y z + (1 / p.θ) * lag0 T y z := by
    funext z; have := Et z; field_simp; linarith
  have hMπ : ∀ x, T.M π x = (-1 / p.θ) * (T.M y x - y x) := fun x => by
    rw [hπf, M_lin, M_lag0]; ring
  have key : ∀ x, p.β * T.M y x - (1 + p.β + p.κ * p.θ) * y x + lag0 T y x = 0 := fun x => by
    have h1 := Epc x
    rw [hMπ x, hπf] at h1
    simp only at h1
    linear_combination (norm := (field_simp; ring)) p.θ * h1
  have hu : ∀ x, y x - z1 p * lag0 T y x = 0 := by
    have hlB : ∀ x, |lag0 T y x| ≤ |B| :=
      abs_lag0_le T (abs_nonneg B) fun x => (hyB x).trans (le_abs_self B)
    refine zero_of_eq_cM T (abs_inv_z2 hp) (A := |B| + z1 p * |B|)
      (g := fun z => y z - z1 p * lag0 T y z) (fun x => ?_) (fun x => ?_)
    · refine (abs_sub _ _).trans (add_le_add ((hyB x).trans (le_abs_self B)) ?_)
      rw [abs_mul, abs_of_pos hz10]
      exact mul_le_mul_of_nonneg_left (hlB x) hz10.le
    · have e : (fun z => y z - z1 p * lag0 T y z) = fun z => 1 * y z + -z1 p * lag0 T y z := by
        funext z; ring
      rw [e, M_lin, M_lag0]
      simp only
      linear_combination (norm := (field_simp; ring)) (-1 / (p.β * z2 p)) * key x +
        (y x / (p.β * z2 p)) * hzs - (lag0 T y x / (p.β * z2 p)) * hzz
  have hy0 : ∀ x, v x 0 = 0 := zero_of_eq_lag T (c := z1 p) (g := y) fun x => by
    linarith [hu x]
  have hyf : (fun z => v z 0) = fun _ => 0 := funext hy0
  have hπ0 : ∀ x, v x 1 = 0 := fun x => by
    have := Et x
    have e1 : y x = 0 := hy0 x
    have e2 : lag0 T y x = 0 := by rw [show y = fun _ => 0 from hyf, lag0_zero]
    have h2 : p.θ * π x = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hθ0
    · exact h
  have hπf0 : (fun z => v z 1) = fun _ => 0 := funext hπ0
  have hF0 : ∀ x, v x 2 = 0 := by
    refine zero_of_eq_cM T (abs_ab hp) (A := B) (g := fun z => v z 2) (fun x => hB x 2)
      fun x => ?_
    have := hRk x 5
    simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, hm, hπf0, M_const, hy0] at this
    linear_combination this
  have hK0 : ∀ x, v x 3 = 0 := fun x => by
    have := hRk x 7
    rw [red_x, hπ0, hF0] at this
    have h2 : (1 - p.α) * (p.θ - 1) / p.c0 * v x 3 = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (div_ne_zero (mul_ne_zero h1α hθ) hc0)
    · exact h
  have hl10 : ∀ x, v x 5 = 0 := fun x => by
    have := red_l1 R hp (lagv T v x) (v x) (Mv T.M v x)
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
    simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, hm, hπf0, M_const, hy0] at this
    linear_combination this
  have hl30 : ∀ x, v x 7 = 0 := fun x => by
    have := hRk x 2
    simp only [DQr, Pi.add_apply, Matrix.cons_val, hl, lag0_zero, hπ0, hF0, hK0, hl10,
      hl40, DNr] at this
    have h2 : (1 - p.α) * ((p.θ - 1) / p.c0) * v x 7 = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero h1α (div_ne_zero hθ hc0))
    · exact h
  funext x k
  fin_cases k
  exacts [hy0 x, hπ0 x, hF0 x, hK0 x, hD x, hl10 x, hl20 x, hl30 x, hl40 x]

/-! ## Linearity, the left inverse and the uniform bound -/

/-- Woodford (2003), §5: the linearisation as one linear map of `(lag, current, expected lead)`. -/
noncomputable def DLin (p : Par) (R : RPar) :
    ((Fin 9 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ)) →ₗ[ℝ] (Fin 9 → ℝ) where
  toFun q := DQr p R q.1 q.2.1 + DNr p R q.2.2
  map_add' q q' := by
    funext i; fin_cases i <;> simp [DQr, DNr] <;> ring
  map_smul' c q := by
    funext i; fin_cases i <;> simp [DQr, DNr] <;> ring

/-- The linearisation is bounded: `‖DQr um u + DNr n‖ ≤ ‖DLin‖ · max(‖um‖, ‖u‖, ‖n‖)`. -/
theorem norm_DLin_le (p : Par) (R : RPar) (um u n : Fin 9 → ℝ) {B : ℝ}
    (h1 : ‖um‖ ≤ B) (h2 : ‖u‖ ≤ B) (h3 : ‖n‖ ≤ B) :
    ‖DQr p R um u + DNr p R n‖ ≤ ‖LinearMap.toContinuousLinearMap (DLin p R)‖ * B := by
  have := (LinearMap.toContinuousLinearMap (DLin p R)).le_opNorm (um, u, n)
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  simp only [Prod.norm_def]
  exact max_le h1 (max_le h2 h3)

/-- The lag of a vector process keeps sup bounds. -/
theorem norm_lagv_le {n : ℕ} {v : X → Fin n → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖v x‖ ≤ B)
    (x : X) : ‖lagv T v x‖ ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB0).2 fun i => ?_
  rw [Real.norm_eq_abs]
  refine abs_lag0_le T hB0 (fun y => ?_) x
  have := (norm_le_pi_norm (v y) i).trans (hB y)
  rwa [Real.norm_eq_abs] at this

/-- The linearised operator is bounded. -/
theorem norm_LR_le (p : Par) (R : RPar) {v : X → Fin 9 → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖v x‖ ≤ B) (x : X) :
    ‖LR T p R v x‖ ≤ ‖LinearMap.toContinuousLinearMap (DLin p R)‖ * B :=
  norm_DLin_le p R _ _ _ (norm_lagv_le T hB0 hB x) (hB x) (Mv_norm_le T.markov hB0 hB x)

/-- The linearised operator is subtractive. -/
theorem LR_sub (p : Par) (R : RPar) (v w : X → Fin 9 → ℝ) (x : X) :
    LR T p R (fun y => v y - w y) x = LR T p R v x - LR T p R w x := by
  have hl : lagv T (fun y => v y - w y) x = lagv T v x - lagv T w x := by
    funext i
    have := lag0_lin T 1 (-1) (fun y => v y i) (fun y => w y i) x
    simp only [lagv, Pi.sub_apply]
    convert this using 2 <;> [funext y; skip] <;> ring
  have hm := congrFun (NonlinearNKMarkovLinks.Mv_sub T.M v w) x
  have e := (DLin p R).map_sub (lagv T v x, v x, Mv T.M v x) (lagv T w x, w x, Mv T.M w x)
  simp only [DLin, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_sub_mk] at e
  simp only [LR, hl, hm]
  exact e

/-- Woodford (2003), App. A.3 (**the uniform bound on the inverse**): `‖L⁻¹r‖ ≤ K‖r‖` with `K`
depending only on the parameters, for every event tree. -/
theorem LinvR_bound {p : Par} (R : RPar) (hp : p.Std) : ∃ K, 0 ≤ K ∧ ∀ {Y : Type*}
    (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y, ‖r y‖ ≤ A) →
      ∀ y, ‖LinvR T p R r y‖ ≤ K * A := by
  obtain ⟨c0, h0, b0⟩ := bd_yv R hp
  obtain ⟨c1, h1, b1⟩ := bd_piv R hp
  obtain ⟨c2, h2, b2⟩ := bd_Fv R hp
  obtain ⟨cx, hx, bx⟩ := bd_xv R hp
  obtain ⟨c4, h4, b4⟩ := bd_Dv hp
  obtain ⟨c5, h5, b5⟩ := bd_l1v R hp
  obtain ⟨cμ, hμ, bμ⟩ := bd_Muv R hp
  obtain ⟨c7, h7, b7⟩ := bd_l3v R hp
  obtain ⟨c8, h8, b8⟩ := bd_l4v R hp
  set K := c0 + c1 + c2 + (c2 + |p.c0| * cx) + c4 + c5 + (cμ + c5) + c7 + c8 with hK
  refine ⟨K, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ y k, |r y k| ≤ A := fun y k => by
    have := (norm_le_pi_norm (r y) k).trans (hr y); rwa [Real.norm_eq_abs] at this
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hc : ∀ c, 0 ≤ c → c * A ≤ K * A → ∀ t : ℝ, |t| ≤ c * A → |t| ≤ K * A :=
    fun c _ hcK t ht => ht.trans hcK
  have hKA : ∀ c, c ≤ K → c * A ≤ K * A := fun c hcK => mul_le_mul_of_nonneg_right hcK hA
  fin_cases i <;> simp only [LinvR, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
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

/-- Woodford (2003), App. A.3 (**the left inverse**): `L⁻¹(Lv) = v` for bounded `v`. -/
theorem LinvR_LR {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    {v : X → Fin 9 → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖v x‖ ≤ B) :
    LinvR T p R (LR T p R v) = v := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound R hp
  set CL := ‖LinearMap.toContinuousLinearMap (DLin p R)‖
  have hLB : ∀ x, ‖LR T p R v x‖ ≤ CL * B := norm_LR_le T p R hB0 hB
  have hLB' : ∀ x k, |LR T p R v x k| ≤ CL * B := fun x k => by
    have := (norm_le_pi_norm (LR T p R v x) k).trans (hLB x); rwa [Real.norm_eq_abs] at this
  have hw := LR_LinvR T R hp hG (LR T p R v) (CL * B) (by positivity) hLB'
  have hbd := hK T (LR T p R v) (CL * B) (by positivity) hLB
  have hz := LR_inj T R hp hG (fun x => v x - LinvR T p R (LR T p R v) x) (B + K * (CL * B))
    (fun x k => by
      have := (norm_le_pi_norm (v x - LinvR T p R (LR T p R v) x) k).trans
        ((norm_sub_le _ _).trans (add_le_add (hB x) (hbd x)))
      rwa [Real.norm_eq_abs] at this)
    (by funext x; rw [LR_sub, hw, sub_self]; rfl)
  funext x
  have := congrFun hz x
  simp only [Pi.zero_apply] at this
  exact (sub_eq_zero.1 this).symm

/-- Woodford (2003), App. A.3: the inverse is subtractive on bounded forcings. -/
theorem LinvR_sub {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    {r r' : X → Fin 9 → ℝ} {A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A') (hr : ∀ x, ‖r x‖ ≤ A)
    (hr' : ∀ x, ‖r' x‖ ≤ A') :
    LinvR T p R (fun x => r x - r' x) = fun x => LinvR T p R r x - LinvR T p R r' x := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound R hp
  have hc : ∀ {s : X → Fin 9 → ℝ} {S : ℝ}, (∀ x, ‖s x‖ ≤ S) → ∀ x k, |s x k| ≤ S :=
    fun hs x k => by
      have := (norm_le_pi_norm _ k).trans (hs x); rwa [Real.norm_eq_abs] at this
  have hw := LR_LinvR T R hp hG r A hA (hc hr)
  have hw' := LR_LinvR T R hp hG r' A' hA' (hc hr')
  have hB : ∀ x, ‖LinvR T p R r x - LinvR T p R r' x‖ ≤ K * A + K * A' := fun x =>
    (norm_sub_le _ _).trans (add_le_add (hK T r A hA hr x) (hK T r' A' hA' hr' x))
  have e := LinvR_LR T R hp hG (by positivity) hB
  rw [← e]
  congr 1
  funext x
  rw [LR_sub, hw, hw']

end Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyTree
