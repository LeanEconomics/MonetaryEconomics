/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergLinks

/-!
# The exact Rotemberg model on the Taylor-principle boundary `κ(φ_π − 1) + (1 − β)φ_y = 0`

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3
(pp. 632–634), for the exact Rotemberg model of `NonlinearRotemberg`. Off the boundary the model is
determinate (`NonlinearRotembergMarkov.markov_equilibrium_general`) or indeterminate
(`NonlinearRotembergIndet.indeterminacy_continuum`). On the boundary the linearised model has a
unit root, so it cannot decide; here the exact model is settled as follows.

## Main results

* **`boundary_linear_kernel`**: on the boundary the linearised operator has a CONSTANT kernel
  vector on every Markov operator (the steady-state Jacobian is singular), and
  **`boundary_left_null`**: a left null vector `ℓ` with `ℓ·DQ_e(1,0,0) = θm(σ+ω) > 0`.
* **`boundary_no_order_eps`** (the whole boundary): for every `K`, there is `ε₀ > 0` such that for
  every constant interest-rate disturbance `ν = ε ∈ (0, ε₀)`, on every nonempty state space with
  every Markov operator (event trees, finite chains, perfect foresight), there is NO exact
  equilibrium with `‖z‖ ≤ Kε`. So no equilibrium selection is Lipschitz (let alone differentiable)
  in the shock: the first-order solution does not exist. (Proof: `V = ℓ·DN z` drifts by at least
  `εθm(σ+ω)/2` per application of the Markov operator, which a bounded `V` cannot do.)
* **`corner_steady`**, **`corner_continuum`** (the corner `φ_π = 1`, `φ_y = 0`): the exact model
  has a CONTINUUM of steady states `π ↦ sss π` through zero; every one is an equilibrium on every
  Markov operator, so for every `r > 0` there are steady-state equilibria with `π ≠ 0` within `r`:
  local uniqueness fails in the exact model.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergBoundary

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov)
open NonlinearNKMarkovGeneral (Mv_const)
open NonlinearRotemberg NonlinearRotembergNewton
open NonlinearRotembergLinks (wedge)

variable {p : Par}

/-! ## The linear structure on the boundary -/

/-- Woodford (2003), Prop. 4.3: the left null vector of the steady-state Jacobian on the boundary,
`ℓ = (θm(σ+ω), φ_y, φ_y θmσ)`. -/
noncomputable def lv (p : Par) : Fin 3 → ℝ :=
  ![p.θ * p.m * (p.σ + p.ω), p.φy, p.φy * (p.θ * p.m * p.σ)]

/-- The pairing `ℓ·w` on `ℝ³`. -/
def dot (l w : Fin 3 → ℝ) : ℝ := l 0 * w 0 + l 1 * w 1 + l 2 * w 2

/-- Woodford (2003), Prop. 4.3 (**the left null vector**): on the boundary
`ℓ·(DQ v + DN v) = 0` for every `v`, and `ℓ·DQ_e(1, 0, 0) = θm(σ+ω)`. -/
theorem boundary_left_null (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (v : Fin 3 → ℝ) :
    dot (lv p) (DQ0 p v) + dot (lv p) (DN0 p v) = 0 ∧
      dot (lv p) (DQe p ![1, 0, 0]) = p.θ * p.m * (p.σ + p.ω) := by
  have hk := hp.κ_mul
  refine ⟨?_, ?_⟩
  · simp only [dot, lv, DQ0, DN0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (v 1 * p.ψ) * hb - (v 1 * (p.φ - 1)) * hk
  · simp [dot, lv, DQe]

/-- Woodford (2003), Prop. 4.3 (**a constant kernel on the boundary**): the constant
`w₀ = ((1−β)ψ, θm(σ+ω), (1−β)ψ)` is in the kernel of the linearised operator on every Markov
operator: the linearised model has a unit root and does not decide determinacy. -/
theorem boundary_linear_kernel (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    {X : Type*} {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) :
    Lop p M (fun _ => ![(1 - p.β) * p.ψ, p.θ * p.m * (p.σ + p.ω), (1 - p.β) * p.ψ]) = 0 := by
  have hk := hp.κ_mul
  funext x i
  simp only [Lop, Pi.add_apply, Pi.zero_apply]
  rw [Mv_const hM]
  fin_cases i <;> simp only [DQ0, DN0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · linear_combination p.ψ * hb - (p.φ - 1) * hk
  · ring
  · ring

/-! ## Tools -/

/-- `|ℓ·w| ≤ (|ℓ₀| + |ℓ₁| + |ℓ₂|)‖w‖`. -/
theorem abs_dot_le (l w : Fin 3 → ℝ) : |dot l w| ≤ (|l 0| + |l 1| + |l 2|) * ‖w‖ := by
  have h : ∀ i, |w i| ≤ ‖w‖ := fun i => norm_le_pi_norm w i
  unfold dot
  calc |l 0 * w 0 + l 1 * w 1 + l 2 * w 2| ≤ |l 0 * w 0| + |l 1 * w 1| + |l 2 * w 2| :=
        (abs_add_le _ _).trans (by linarith [abs_add_le (l 0 * w 0) (l 1 * w 1)])
    _ ≤ |l 0| * ‖w‖ + |l 1| * ‖w‖ + |l 2| * ‖w‖ := by
        rw [abs_mul, abs_mul, abs_mul]
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (h 0) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (h 1) (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left (h 2) (abs_nonneg _))
    _ = _ := by ring

/-- `ℓ·(Mv h) = M(ℓ·h)`. -/
theorem dot_Mv {X : Type*} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (l : Fin 3 → ℝ) (h : X → Fin 3 → ℝ)
    (x : X) : dot l (Mv M h x) = M (fun x' => dot l (h x')) x := by
  have e : (fun x' => dot l (h x')) = l 0 • (fun x' => h x' 0) + l 1 • (fun x' => h x' 1) +
      l 2 • (fun x' => h x' 2) := by funext x'; simp [dot]
  rw [e, map_add, map_add, map_smul, map_smul, map_smul]
  simp [dot, Mv]

/-- A Markov operator maps constants to themselves. -/
theorem M_const {X : Type*} {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) (c : ℝ) (x : X) :
    M (fun _ => c) x = c := by
  have : (fun _ : X => c) = c • (fun _ => (1 : ℝ)) := by funext; simp
  rw [this, map_smul, hM.1]; simp

/-- A Markov operator is positive on bounded functions. -/
theorem M_nonneg {X : Type*} {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) {h : X → ℝ} {C : ℝ}
    (h0 : ∀ x, 0 ≤ h x) (hC : ∀ x, h x ≤ C) (x : X) : 0 ≤ M h x := by
  have hb : ∀ x, |h x - C / 2| ≤ C / 2 := fun x => by
    rw [abs_le]; constructor <;> linarith [h0 x, hC x]
  have e : (fun x => h x - C / 2) = h - (fun _ => C / 2) := rfl
  have := hM.2 _ _ hb x
  rw [e, map_sub, Pi.sub_apply, M_const hM, abs_le] at this
  linarith [this.1]

/-- Woodford (2003), App. A.3 (tool): the first-order remainder is small near the base point. -/
theorem small_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : DifferentiableAt ℝ g 0) {η : ℝ}
    (hη : 0 < η) : ∃ ρ > 0, ∀ x, ‖x‖ < ρ → ‖g x - g 0 - fderiv ℝ g 0 x‖ ≤ η * ‖x‖ := by
  have h := hg.hasFDerivAt.isLittleO.def hη
  obtain ⟨ρ, hρ, h'⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  have := h' (by simpa [dist_zero_right] using hx)
  simpa using this

/-- The derivative of `Q` at the steady state, split into its disturbance and state parts. -/
theorem fderiv_Qmap_apply (e w : Fin 3 → ℝ) :
    fderiv ℝ (Qmap p) 0 (e, w) = DQe p e + DQ0 p w := by
  have h : ((e, w) : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = (e, 0) + (0, w) := by simp
  rw [h, map_add, show (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = (0, 0) from rfl, fderiv_Qmap_inl,
    fderiv_Qmap_inr]

/-- The derivative of `N` at the steady state (it does not depend on the disturbances). -/
theorem fderiv_Nmap_apply (e w : Fin 3 → ℝ) : fderiv ℝ (Nmap p) 0 (e, w) = DN0 p w := by
  have h : ((e, w) : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = (e, 0) + (0, w) := by simp
  rw [h, map_add, show (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = (0, 0) from rfl, fderiv_Nmap_inl,
    fderiv_Nmap_inr, zero_add]

/-- `‖DN v‖ ≤ (σ + 1 + βψ)‖v‖`. -/
theorem norm_DN0_le (hp : p.Basic) (v : Fin 3 → ℝ) :
    ‖DN0 p v‖ ≤ (p.σ + 1 + p.β * p.ψ) * ‖v‖ := by
  have h : ∀ i, |v i| ≤ ‖v‖ := fun i => norm_le_pi_norm v i
  have hβψ : 0 ≤ p.β * p.ψ := mul_nonneg hp.β_pos.le hp.ψ_pos.le
  have hv := norm_nonneg v
  have hs := hp.σ_pos
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i <;> simp only [DN0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · calc |-(p.σ * v 2) - v 1| ≤ |p.σ * v 2| + |v 1| := by
          rw [sub_eq_add_neg, ← neg_add]; rw [abs_neg]; exact abs_add_le _ _
      _ ≤ p.σ * ‖v‖ + ‖v‖ := by
          rw [abs_mul, abs_of_pos hs]
          exact add_le_add (mul_le_mul_of_nonneg_left (h 2) hs.le) (h 1)
      _ ≤ _ := by nlinarith
  · rw [abs_neg, abs_mul, abs_of_nonneg hβψ]
    nlinarith [h 1]
  · simp only [abs_zero]; positivity

/-! ## No equilibrium of order `ε` on the boundary -/

/-- Woodford (2003), Prop. 4.3 and App. A.3 (**on the boundary the exact model has no equilibrium
of the order of the shock**): if `κ(φ_π − 1) + (1 − β)φ_y = 0`, then for every `K ≥ 0` there is
`ε₀ > 0` such that for every constant interest-rate disturbance `ν = ε ∈ (0, ε₀)`, on every
nonempty state space with every Markov operator, no process `z` with `‖z‖ ≤ Kε` solves the exact
conditions. Hence no equilibrium selection is Lipschitz in the shock at `ε = 0`. -/
theorem boundary_no_order_eps (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ ε0 > 0, ∀ ε, 0 < ε → ε < ε0 → ∀ (X : Type) [Nonempty X] (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)),
      IsMarkov M → ∀ z : X → Fin 3 → ℝ, (∀ x, ‖z x‖ ≤ K * ε) →
        PhiG (Qmap p) (Nmap p) M (fun _ => ε • ![1, 0, 0]) z ≠ 0 := by
  set a := p.θ * p.m * (p.σ + p.ω) with ha
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have ha0 : 0 < a := mul_pos hθm hs
  set l := lv p
  set L := |l 0| + |l 1| + |l 2| with hL
  have hl0 : l 0 = a := rfl
  have hL0 : 0 < L := by
    have : 0 < |l 0| := by rw [hl0, abs_of_pos ha0]; exact ha0
    positivity
  set η := a / (8 * L * (1 + K)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := small_remainder
    ((contDiff_Qmap (p := p) (n := 1)).differentiable one_ne_zero 0) hη0
  obtain ⟨ρN, hρN, hN⟩ := small_remainder
    ((contDiff_Nmap (p := p) (n := 1)).differentiable one_ne_zero 0) hη0
  refine ⟨min ρQ ρN / (1 + K), by positivity, fun ε hε hεs X _ M hM z hz heq => ?_⟩
  set e : Fin 3 → ℝ := ε • ![1, 0, 0] with he
  have hen : ‖e‖ ≤ ε := by
    refine (pi_norm_le_iff_of_nonneg hε.le).2 fun i => ?_
    fin_cases i <;> simp [he, abs_of_pos hε, hε.le]
  have hsmall : ∀ x, ‖((e, z x) : (Fin 3 → ℝ) × (Fin 3 → ℝ))‖ ≤ (1 + K) * ε := fun x => by
    rw [Prod.norm_def]
    exact max_le (by nlinarith) (by nlinarith [hz x])
  have hlt : (1 + K) * ε < min ρQ ρN := by
    rw [lt_div_iff₀ (by positivity)] at hεs; linarith
  -- the remainders
  set rq : X → ℝ := fun x => dot l (Qmap p (e, z x) - Qmap p 0 - (DQe p e + DQ0 p (z x)))
  set rn : X → ℝ := fun x => dot l (Nmap p (e, z x) - Nmap p 0 - DN0 p (z x))
  have hrq : ∀ x, |rq x| ≤ L * (η * ((1 + K) * ε)) := fun x => by
    have h1 := hQ (e, z x) ((hsmall x).trans_lt (hlt.trans_le (min_le_left _ _)))
    rw [fderiv_Qmap_apply] at h1
    refine (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_left (h1.trans ?_) hL0.le)
    exact mul_le_mul_of_nonneg_left (hsmall x) hη0.le
  have hrn : ∀ x, |rn x| ≤ L * (η * ((1 + K) * ε)) := fun x => by
    have h1 := hN (e, z x) ((hsmall x).trans_lt (hlt.trans_le (min_le_right _ _)))
    rw [fderiv_Nmap_apply] at h1
    refine (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_left (h1.trans ?_) hL0.le)
    exact mul_le_mul_of_nonneg_left (hsmall x) hη0.le
  set V : X → ℝ := fun x => dot l (DN0 p (z x)) with hV
  have hss := steadyState_zero (p := p)
  have hnull := fun v => (boundary_left_null hp hb v).1
  have hdqe : dot l (DQe p e) = ε * a := by
    simp [l, he, dot, lv, DQe, ha]
    ring
  -- the drift of `V`
  have hdrift : ∀ x, M V x - V x ≤ -(ε * a / 2) := fun x => by
    have h0 := congrFun (congrFun heq x)
    have hd : dot l (PhiG (Qmap p) (Nmap p) M (fun _ => e) z x) = 0 := by
      rw [show PhiG (Qmap p) (Nmap p) M (fun _ => e) z x = 0 from congrFun heq x]
      simp [dot]
    simp only [PhiG] at hd
    have hdot_add : ∀ u w, dot l (u + w) = dot l u + dot l w := fun u w => by
      simp only [dot, Pi.add_apply]; ring
    have hdot_sub : ∀ u w, dot l (u - w) = dot l u - dot l w := fun u w => by
      simp only [dot, Pi.sub_apply]; ring
    rw [hdot_add, dot_Mv] at hd
    have hq : dot l (Qmap p (e, z x)) = dot l (Qmap p 0) + ε * a - V x + rq x := by
      simp only [rq, hdot_sub, hdot_add, hdqe, V]
      have := hnull (z x)
      linarith
    have hn : (fun x' => dot l (Nmap p (e, z x'))) =
        (fun _ => dot l (Nmap p 0)) + V + rn := by
      funext x'
      simp only [rn, Pi.add_apply, hdot_sub, V]
      ring
    rw [hn, map_add, map_add] at hd
    simp only [Pi.add_apply] at hd
    rw [M_const hM, hq] at hd
    have hz0 : dot l (Qmap p 0) + dot l (Nmap p 0) = 0 := by
      rw [← hdot_add, show (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = (0, 0) from rfl, hss]
      simp [dot]
    have hMrn : |M rn x| ≤ L * (η * ((1 + K) * ε)) := hM.2 rn _ hrn x
    have hc : 2 * (L * (η * ((1 + K) * ε))) = ε * a / 4 := by
      rw [hη]; field_simp; ring
    have h3 := (abs_le.1 (hrq x)).1
    have h4 := (abs_le.1 hMrn).1
    have key : M V x - V x = -(ε * a) - rq x - M rn x := by linear_combination hd - hz0
    rw [key]
    have hea : 0 < ε * a := mul_pos hε ha0
    linarith
  -- `V` is bounded
  set BV := L * ((p.σ + 1 + p.β * p.ψ) * (K * ε))
  have hVb : ∀ x, |V x| ≤ BV := fun x => by
    refine (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0.le)
    exact (norm_DN0_le hp _).trans (mul_le_mul_of_nonneg_left (hz x)
      (by have := hp.σ_pos; have := mul_nonneg hp.β_pos.le hp.ψ_pos.le; linarith))
  have hBV : 0 ≤ BV := (abs_nonneg _).trans (hVb (Classical.arbitrary X))
  set δ := ε * a / 2
  have hδ : 0 < δ := by positivity
  -- iterate the Markov operator
  have hit : ∀ n : ℕ, ∀ x, |(M ^ n) V x| ≤ BV ∧ (M ^ n) V x ≤ V x - n * δ := by
    intro n
    induction n with
    | zero => intro x; simp [hVb x]
    | succ n ih =>
      intro x
      have hpow : (M ^ (n + 1)) V = M ((M ^ n) V) := by
        rw [pow_succ', Module.End.mul_apply]
      rw [hpow]
      refine ⟨hM.2 _ _ (fun y => (ih y).1) x, ?_⟩
      have hn0 : (0 : ℝ) ≤ n * δ := by positivity
      have hpos : 0 ≤ M (fun y => V y - n * δ - (M ^ n) V y) x :=
        M_nonneg hM (fun y => by linarith [(ih y).2]) (C := 2 * BV + n * δ)
          (fun y => by
            have := abs_le.1 (hVb y); have := abs_le.1 (ih y).1; linarith) x
      have e : (fun y => V y - n * δ - (M ^ n) V y) = V - (fun _ => n * δ) - (M ^ n) V := rfl
      rw [e, map_sub, map_sub, Pi.sub_apply, Pi.sub_apply, M_const hM] at hpos
      have := hdrift x
      push_cast
      linarith
  obtain ⟨x0⟩ := ‹Nonempty X›
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * BV + 1) / δ)
  have h1 := hit n x0
  have h2 := abs_le.1 h1.1
  have h3 := abs_le.1 (hVb x0)
  rw [div_lt_iff₀ hδ] at hn
  linarith [h1.2]

/-! ## The corner `φ_π = 1`, `φ_y = 0`: a continuum of steady states -/

/-- Woodford (2003), Ch. 4 (2.7) at `φ_π = 1`, `φ_y = 0`: steady-state output at inflation `π`,
`ŷ(π) = (log(1 + (1−β)ψ(e^π − 1)e^π/(θm)) − σ log(C/Y))/(σ + ω)`. -/
noncomputable def ssY (p : Par) (π : ℝ) : ℝ :=
  (Real.log (1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m)) -
    p.σ * Real.log (wedge p.ψ π)) / (p.σ + p.ω)

/-- Woodford (2003), Ch. 4 (2.7) at `φ_π = 1`, `φ_y = 0`: the steady state with inflation `π`,
`(ŷ(π), π, ŷ(π) + log(C/Y))`. -/
noncomputable def sss (p : Par) (π : ℝ) : Fin 3 → ℝ :=
  ![ssY p π, π, ssY p π + Real.log (wedge p.ψ π)]

/-- Woodford (2003), Ch. 4 (2.7) and Rotemberg (1982) (**every inflation rate is a steady state at
the corner**): if `φ_π = 1`, `φ_y = 0`, then for every `π` with `C/Y > 0` and
`1 + (1−β)ψ(e^π − 1)e^π/(θm) > 0`, `sss π` solves the exact conditions without disturbances. -/
theorem corner_steady (hp : p.Basic) (hφ : p.φ = 1) (hφy : p.φy = 0) (π : ℝ)
    (hw : 0 < wedge p.ψ π)
    (hk : 0 < 1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m)) :
    Qmap p (0, sss p π) + Nmap p (0, sss p π) = 0 := by
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm : p.m ≠ 0 := hp.m_pos.ne'
  set Y := ssY p π with hY
  set C := Y + Real.log (wedge p.ψ π) with hC
  have hYs : (p.σ + p.ω) * Y = Real.log (1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) *
      Real.exp π) / (p.θ * p.m)) - p.σ * Real.log (wedge p.ψ π) := by
    rw [hY, ssY]; field_simp
  have hexp : Real.exp ((1 + p.ω) * Y) = Real.exp (Y - p.σ * C) *
      (1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m)) := by
    rw [← Real.exp_log hk, ← Real.exp_add]
    congr 1
    rw [hC]; linear_combination hYs
  have hEC : Real.exp C = Real.exp Y * wedge p.ψ π := by
    rw [hC, Real.exp_add, Real.exp_log hw]
  funext i
  fin_cases i
  · simp only [Qmap, Nmap, sss, Fin.zero_eta, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, hφ, hφy, ← hY, ← hC]
    rw [show -(1 * π + 0 * Y + 0 + p.σ * C) = -(p.σ * C) - π by ring]; ring
  · simp only [Qmap, Nmap, sss, Gadj, Hmc, Fin.mk_one, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Pi.zero_apply, ← hY, ← hC, add_zero, sub_zero,
      mul_zero]
    rw [hexp]
    field_simp
    ring
  · simp only [Qmap, Nmap, sss, Fin.reduceFinMk, Pi.add_apply, Matrix.cons_val, Pi.zero_apply,
      ← hY, ← hC, add_zero]
    rw [hEC]; unfold wedge; ring

/-- `sss 0 = 0`. -/
theorem sss_zero : sss p 0 = 0 := by
  funext i; fin_cases i <;> simp [sss, ssY, wedge]

/-- Woodford (2003), Ch. 4 (**the continuum of steady-state equilibria at the corner**): if
`φ_π = 1` and `φ_y = 0`, there is `ρ > 0` such that for every `|π| < ρ` the constant process
`sss π` is an exact equilibrium without disturbances on every Markov operator, distinct values of
`π` give distinct equilibria, and for every `r > 0` some equilibrium with `π ≠ 0` lies within `r`
of the steady state: local uniqueness fails in the exact model. -/
theorem corner_continuum (hp : p.Basic) (hφ : p.φ = 1) (hφy : p.φy = 0) :
    ∃ ρ > 0, (∀ π, |π| < ρ → ∀ (X : Type) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      PhiG (Qmap p) (Nmap p) M (fun _ => 0) (fun _ => sss p π) = 0) ∧
      (∀ π π', sss p π = sss p π' → π = π') ∧
      ∀ r > 0, ∃ π, π ≠ 0 ∧ |π| < ρ ∧ ‖sss p π‖ ≤ r := by
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  -- positivity of the two arguments near zero
  have hc1 : Continuous fun π : ℝ => wedge p.ψ π := by unfold wedge; fun_prop
  have hc2 : Continuous fun π : ℝ =>
      1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m) := by fun_prop
  have hev : ∀ᶠ π in 𝓝 (0 : ℝ), 0 < wedge p.ψ π ∧
      0 < 1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m) := by
    refine (hc1.continuousAt.eventually (lt_mem_nhds ?_)).and
      (hc2.continuousAt.eventually (lt_mem_nhds ?_))
    · simp [wedge]
    · simp
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ρ, hρ, fun π hπ X M hM => ?_, fun π π' h => ?_, fun r hr => ?_⟩
  · have hpos := hball (by simpa [Real.dist_eq] using hπ)
    have hst := corner_steady hp hφ hφy π hpos.1 hpos.2
    funext x
    simp only [PhiG, Pi.zero_apply]
    rw [Mv_const hM]
    exact hst
  · have := congrFun h 1
    simpa [sss] using this
  · -- continuity of `sss` at zero
    have hcont : ContinuousAt (sss p) 0 := by
      have h1 : ContinuousAt (ssY p) 0 := by
        unfold ssY
        refine ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) _
        · exact (hc2.continuousAt).log (by simp)
        · exact (hc1.continuousAt.log (by simp [wedge])).const_mul _
      refine continuousAt_pi.2 fun i => ?_
      fin_cases i
      · exact h1
      · exact continuousAt_id
      · exact h1.add (hc1.continuousAt.log (by simp [wedge]))
    have ht : Tendsto (sss p) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto; rwa [sss_zero] at this
    have h1 : ∀ᶠ π in 𝓝 (0 : ℝ), ‖sss p π‖ ≤ r ∧ |π| < ρ :=
      (ht.eventually (Metric.closedBall_mem_nhds 0 hr)).and
        (Metric.ball_mem_nhds 0 hρ) |>.mono fun π h => ⟨by simpa using h.1, by simpa using h.2⟩
    have h2 : ∀ᶠ π in 𝓝[≠] (0 : ℝ), (‖sss p π‖ ≤ r ∧ |π| < ρ) ∧ π ∈ ({0}ᶜ : Set ℝ) :=
      (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨π, hπ, hne⟩ := h2.exists
    exact ⟨π, hne, hπ.2, hπ.1⟩

end Woodford.StabilizationWelfare.NonlinearRotembergBoundary
