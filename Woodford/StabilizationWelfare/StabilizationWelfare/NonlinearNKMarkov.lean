/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Determinacy
import StabilizationWelfare.Moments
import StabilizationWelfare.OneParamTaylor
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# A Markov equilibrium of the exact nonlinear New Keynesian model

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392: the welfare approximations
are taken "along a one-parameter family of economies" whose equilibria are assumed to exist and
to be smooth in the amplitude of the disturbances), §5 (pp. 455–463: the exact Calvo model under
Assumption 6.2, (5.4)), and Appendix E; Chapter 3, §2 (the Calvo model), Chapter 4, §2.2
(the Taylor principle, Proposition 4.3) and Appendix A.3 (local determinacy by the implicit
function theorem).

The exact model (log deviations from the zero-inflation steady state, Assumption 6.2, no
government purchases, `s_C = 1`):

* household Euler equation with the interest-rate rule
  `1 + i_t = β⁻¹ Π_t^{φ_π} (Y_t/Ȳ)^{φ_y} e^{ν_t}` substituted:
  `E_t[exp(−σ(ŷ_{t+1} − ĉ_{t+1}) − π_{t+1})] = exp(−(φ_π π_t + φ_y ŷ_t + ν_t + σ(ŷ_t − ĉ_t)))`
  (`σ` is Woodford's `σ⁻¹ = σ̃` with `s_C = 1`, `ĉ` the preference shock);
* the Calvo recursions for the auxiliary sums `F`, `K` of the reset problem
  (`LargeDistortions.RecEq`):
  `e^{F̂_t} = (1−αβ)e^{f̂_t} + αβ E_t e^{(θ−1)π_{t+1} + F̂_{t+1}}`,
  `e^{K̂_t} = (1−αβ)e^{k̂_t} + αβ E_t e^{θ(1+ω)π_{t+1} + K̂_{t+1}}`, with
  `f̂ = (1−σ)ŷ + σĉ + τ̂` (`LargeDistortions.fhatIso` at `s_C = 1`, `Ĝ = 0`) and
  `k̂ = (1+ω)ŷ − ωq + μ̂ʷ`;
* the price index with the optimal reset price `(1+ωθ)x̂ = K̂ − F̂` substituted:
  `α(e^{(θ−1)π_t} − 1) + (1−α)(e^{−(θ−1)(K̂_t − F̂_t)/(1+ωθ)} − 1) = 0`;
* the price-dispersion law of motion `Δ_t = αΔ_{t−1}e^{θ(1+ω)π_t} + (1−α)e^{−θ(1+ω)x̂_t}`
  (the endogenous state; module `NonlinearNKMarkovLinks`).

The exogenous state follows a Markov chain on a FINITE set `S` with transition matrix `P`; the
disturbances are `ε ξ(s)` with `ξ : S → ℝ⁵` (`ν, ĉ, τ̂, q, μ̂ʷ`) — bounded support, amplitude
`ε` (the `σ` of "shocks of scale `σ`"; `σ` is reserved here for the elasticity). A Markov
equilibrium is a time-invariant policy function of the exogenous state solving the conditions
state by state, with `E_t` the transition operator.

## Method

The conditions at a state `x` of an ARBITRARY state space `X` with an ARBITRARY Markov operator
`M` (linear, `M 1 = 1`, sup-norm contraction: `IsMarkov`) are
`Q(εξ(x), z(x)) + M[N(εξ, z)](x) = 0` with fixed smooth `Q, N : ℝ⁵ × ℝ⁴ → ℝ⁴` (`Qmap`,
`Nmap`). The linearised operator `Lop` is `v ↦ DQ v + M[DN v]` (`DQ0`, `DN0`).

* `apriori`: under the Taylor principle `κ(φ_π − 1) + (1 − β)φ_y > 0` there is a constant `K`
  depending only on the parameters with `‖v‖ ≤ K ‖Lop v‖` for EVERY state space and EVERY Markov
  operator. The proof reduces `Lop` to the 2×2 IS–AS block `u = A M u + b` (`Amat`), with `A`
  Schur stable exactly by the Taylor principle (`schurStable_Amat`, Proposition 4.3), so
  `Aⁿ → 0` and `u = ∑_{k<n} Aᵏ Mᵏ b + Aⁿ Mⁿ u` (`iterate_eq`); the auxiliary sums have root
  `αβ < 1`.
* `markov_equilibrium`: on a finite chain the residual map is `C^∞`, its derivative at the steady
  state is injective by `apriori`, hence invertible (finite dimension), and Mathlib's inverse
  function theorem (`ContDiffAt.toOpenPartialHomeomorph`, `ContDiffAt.to_localInverse`) applied
  to `(ε, z) ↦ (ε, Φ(ε, z))` gives: for `|ε|` small a Markov equilibrium `zε` exists, it is the
  unique one in a fixed ball around the steady state, `ε ↦ zε` is `C²`, and `z₀ = 0` (the
  deterministic steady state is the base point).
* `firstOrder`: the derivative `z′(0)` solves the log-linear Markov NK model
  (IS curve with the rule, NKPC `π = κ(ŷ − ŷⁿ) + βPπ`).
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkov

open Filter Topology Asymptotics

/-! ## Parameters -/

/-- Woodford (2003), Ch. 3 and §5 (Assumption 6.2): the structural parameters — the Calvo
probability `α`, the discount factor `β`, the elasticity of substitution `θ`, the elasticity `ω`
of real marginal cost, the inverse intertemporal elasticity `σ` (`σ⁻¹` in the book), and the
interest-rate rule coefficients `φ_π`, `φ_y`. -/
structure Par where
  /-- The Calvo probability of not resetting the price. -/
  α : ℝ
  /-- The discount factor. -/
  β : ℝ
  /-- The elasticity of substitution between goods. -/
  θ : ℝ
  /-- The elasticity of real marginal cost with respect to own output. -/
  ω : ℝ
  /-- The inverse of the intertemporal elasticity of substitution (`σ⁻¹`). -/
  σ : ℝ
  /-- The response of the interest rate to inflation. -/
  φ : ℝ
  /-- The response of the interest rate to output. -/
  φy : ℝ

namespace Par

variable (p : Par)

/-- Woodford (2003), (2.19) of Ch. 3 and p. 400: the slope of the NKPC,
`κ = (1−α)(1−αβ)/α · (ω + σ)/(1 + ωθ)` (`Moments.calvoKappa`). -/
noncomputable def κ : ℝ := Moments.calvoKappa p.α p.β p.ω p.θ p.σ

/-- Woodford (2003), Ch. 4, Proposition 4.3, eq. (2.7), p. 254: the maintained assumptions, with
the Taylor principle in the form `κ(φ_π − 1) + (1 − β)φ_y > 0` (both responses nonnegative). This
is (2.7), `φ_π + (1 − β)φ_x/(4κ) > 1`, with the rule written in quarterly rates (`φ_y = φ_x/4`). -/
structure Std where
  α_pos : 0 < p.α
  α_lt_one : p.α < 1
  β_pos : 0 < p.β
  β_lt_one : p.β < 1
  one_lt_θ : 1 < p.θ
  ω_nonneg : 0 ≤ p.ω
  σ_pos : 0 < p.σ
  φ_nonneg : 0 ≤ p.φ
  φy_nonneg : 0 ≤ p.φy
  taylor : 0 < p.κ * (p.φ - 1) + (1 - p.β) * p.φy

/-- Woodford (2003), §5: `1 + ωθ`, the exponent of the reset condition. -/
def c0 : ℝ := 1 + p.ω * p.θ

/-- Woodford (2003), §5: the coefficient `c = (1+ωθ)α/(1−α)` linking the reset-price gap to
inflation through the linearised price index. -/
noncomputable def cR : ℝ := p.c0 * p.α / (1 - p.α)

/-- The coefficient `(1+ωθ)/((1−α)(θ−1))` of the price-index residual. -/
noncomputable def k3 : ℝ := p.c0 / ((1 - p.α) * (p.θ - 1))

/-- The determinant `σ + φ_y + φ_π κ` of the current-period block of the IS–AS system. -/
noncomputable def dd : ℝ := p.σ + p.φy + p.φ * p.κ

variable {p}

/-- Woodford (2003), §5: `1 + ωθ > 0`. -/
theorem Std.c0_pos (hp : p.Std) : 0 < p.c0 := by
  have := mul_nonneg hp.ω_nonneg (by linarith [hp.one_lt_θ] : (0 : ℝ) ≤ p.θ)
  unfold c0; linarith

/-- Woodford (2003), Ch. 3, (2.19): the NKPC slope is positive, `κ > 0`. -/
theorem Std.κ_pos (hp : p.Std) : 0 < p.κ := by
  unfold κ Moments.calvoKappa
  have h1 : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  have h2 : 0 < 1 - p.α * p.β := by nlinarith [hp.α_lt_one, hp.β_lt_one, hp.α_pos, hp.β_pos]
  have h3 : 0 < p.ω + p.σ := by linarith [hp.ω_nonneg, hp.σ_pos]
  have h4 : 0 < 1 + p.ω * p.θ := hp.c0_pos
  have := hp.α_pos
  positivity

/-- Woodford (2003), §5: `c = (1+ωθ)α/(1−α) > 0`. -/
theorem Std.cR_pos (hp : p.Std) : 0 < p.cR := by
  unfold cR
  have := hp.c0_pos; have := hp.α_pos; have : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  positivity

/-- Woodford (2003), Proposition 4.3: `σ + φ_y + φ_π κ > 0`. -/
theorem Std.dd_pos (hp : p.Std) : 0 < p.dd := by
  unfold dd
  have := mul_nonneg hp.φ_nonneg hp.κ_pos.le
  linarith [hp.σ_pos, hp.φy_nonneg]

/-- Woodford (2003), Ch. 3: `αβ < 1`, the discount factor of the reset problem. -/
theorem Std.ab_lt_one (hp : p.Std) : p.α * p.β < 1 := by
  nlinarith [hp.α_lt_one, hp.β_lt_one, hp.α_pos, hp.β_pos]

/-- Woodford (2003), Ch. 3: `αβ > 0`. -/
theorem Std.ab_pos (hp : p.Std) : 0 < p.α * p.β := mul_pos hp.α_pos hp.β_pos

/-- Woodford (2003), §5 (the algebra behind the NKPC): `αβ(1+ωθ + c) = βc`. -/
theorem Std.ab_c (hp : p.Std) : p.α * p.β * (p.c0 + p.cR) = p.β * p.cR := by
  unfold cR
  have : (1 - p.α) ≠ 0 := by linarith [hp.α_lt_one]
  field_simp
  ring

/-- Woodford (2003), §5: `κ = (1−αβ)(ω + σ)/c`. -/
theorem Std.κ_eq (hp : p.Std) : p.κ = (1 - p.α * p.β) * (p.ω + p.σ) / p.cR := by
  unfold κ Moments.calvoKappa cR c0
  have : (1 - p.α) ≠ 0 := by linarith [hp.α_lt_one]
  have : p.α ≠ 0 := hp.α_pos.ne'
  have : 1 + p.ω * p.θ ≠ 0 := hp.c0_pos.ne'
  field_simp

end Par

/-! ## Markov operators

A Markov operator on bounded functions of a state space `X` is a linear map with `M 1 = 1`
that does not increase sup-norm bounds; `E_t[h(x_{t+1})] = (Mh)(x_t)`. -/

variable {X : Type*}

/-- Woodford (2003), App. A.3 (rational expectations on a Markov state): `M` is a Markov
operator — linear, `M 1 = 1`, and `|h| ≤ C ⇒ |Mh| ≤ C`. -/
def IsMarkov (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop :=
  M (fun _ => 1) = (fun _ => 1) ∧ ∀ (h : X → ℝ) (C : ℝ), (∀ x, |h x| ≤ C) → ∀ x, |M h x| ≤ C

/-- The Markov operator applied coordinatewise to a vector-valued function. -/
def Mv {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (h : X → Fin n → ℝ) : X → Fin n → ℝ :=
  fun x i => M (fun x' => h x' i) x

/-- A Markov operator keeps sup-norm bounds of vector-valued functions. -/
theorem Mv_norm_le {n : ℕ} {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {h : X → Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C) (hh : ∀ x, ‖h x‖ ≤ C) (x : X) :
    ‖Mv M h x‖ ≤ C := by
  refine (pi_norm_le_iff_of_nonneg hC).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact hM.2 _ C (fun x' => by
    have := norm_le_pi_norm (h x') i
    rw [Real.norm_eq_abs] at this
    exact this.trans (hh x')) x

/-- `Mv` is additive. -/
theorem Mv_add {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (h k : X → Fin n → ℝ) :
    Mv M (fun x => h x + k x) = fun x => Mv M h x + Mv M k x := by
  funext x i
  simp only [Mv, Pi.add_apply]
  have : (fun x' => h x' i + k x' i) = (fun x' => h x' i) + fun x' => k x' i := rfl
  rw [this, map_add]
  rfl

/-- `Mv` commutes with a constant matrix. -/
theorem Mv_mulVec {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (B : Matrix (Fin n) (Fin n) ℝ)
    (h : X → Fin n → ℝ) : Mv M (fun x => B.mulVec (h x)) = fun x => B.mulVec (Mv M h x) := by
  funext x i
  simp only [Mv, Matrix.mulVec, dotProduct]
  have : (fun x' => ∑ j, B i j * h x' j) = ∑ j, B i j • fun x' => h x' j := by
    funext x'; simp [Finset.sum_apply]
  rw [this, map_sum]
  simp [Finset.sum_apply, map_smul]

/-- Woodford (2003), App. A.3: the transition operator `(Ph)(s) = ∑_{s'} P(s,s') h(s')` of a
finite Markov chain. -/
noncomputable def chainOp {S : Type*} [Fintype S] (P : S → S → ℝ) : (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun h s := ∑ s', P s s' * h s'
  map_add' h k := by funext s; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c h := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Woodford (2003), App. A.3: a stochastic matrix (`P ≥ 0`, rows summing to one). -/
def Stochastic {S : Type*} [Fintype S] (P : S → S → ℝ) : Prop :=
  (∀ s s', 0 ≤ P s s') ∧ ∀ s, ∑ s', P s s' = 1

/-- Woodford (2003), App. A.3: the transition operator of a stochastic matrix is Markov. -/
theorem chainOp_isMarkov {S : Type*} [Fintype S] {P : S → S → ℝ} (hP : Stochastic P) :
    IsMarkov (chainOp P) := by
  refine ⟨?_, fun h C hC s => ?_⟩
  · funext s; simp [chainOp, hP.2 s]
  · change |∑ s', P s s' * h s'| ≤ C
    calc |∑ s', P s s' * h s'| ≤ ∑ s', |P s s' * h s'| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', P s s' * C := Finset.sum_le_sum fun s' _ => by
          rw [abs_mul, abs_of_nonneg (hP.1 s s')]
          exact mul_le_mul_of_nonneg_left (hC s') (hP.1 s s')
      _ = C := by rw [← Finset.sum_mul, hP.2 s, one_mul]

/-! ## Bounds improved by a contraction -/

/-- If every bound `U` of `‖f‖` improves to `b + qU` with `0 ≤ q < 1`, then `‖f‖ ≤ b/(1−q)`. -/
theorem bound_of_improve {E : Type*} [Norm E] {f : X → E} {b q U0 : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hU0 : ∀ x, ‖f x‖ ≤ U0)
    (himp : ∀ U, (∀ x, ‖f x‖ ≤ U) → ∀ x, ‖f x‖ ≤ b + q * U) (x : X) :
    ‖f x‖ ≤ b / (1 - q) := by
  have hn : ∀ n : ℕ, ∀ x, ‖f x‖ ≤ b / (1 - q) + q ^ n * (U0 - b / (1 - q)) := by
    intro n
    induction n with
    | zero => intro x; simpa using hU0 x
    | succ n ih =>
      intro x
      have h := himp _ ih x
      have : b + q * (b / (1 - q) + q ^ n * (U0 - b / (1 - q))) =
          b / (1 - q) + q ^ (n + 1) * (U0 - b / (1 - q)) := by
        have : 1 - q ≠ 0 := by linarith
        field_simp
        ring
      linarith
  have ht : Tendsto (fun n : ℕ => b / (1 - q) + q ^ n * (U0 - b / (1 - q))) atTop
      (𝓝 (b / (1 - q) + 0 * (U0 - b / (1 - q)))) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _)
  rw [zero_mul, add_zero] at ht
  exact ge_of_tendsto' ht fun n => hn n x

/-! ## The IS–AS block and the Taylor principle -/

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) in Markov form: the matrix `A = B₀⁻¹B₁` of the IS–AS
block `u = A M u + b`, `u = (ŷ, π)`:
`A = (σ + φ_y + φ_π κ)⁻¹ [[σ, 1 − φ_π β], [κσ, κ + β(σ + φ_y)]]`. -/
noncomputable def Amat (p : Par) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.σ / p.dd, (1 - p.φ * p.β) / p.dd; p.κ * p.σ / p.dd, (p.κ + p.β * (p.σ + p.φy)) / p.dd]

variable {p : Par}

/-- Woodford (2003), Proposition 4.3, p. 254 (**the Taylor principle is exactly Schur stability
of the IS–AS block**): under `κ(φ_π − 1) + (1 − β)φ_y > 0`, `A` has both eigenvalues inside the
unit circle. -/
theorem schurStable_Amat (hp : p.Std) : SchurStable (tr2 (Amat p)) (det2 (Amat p)) := by
  have hd := hp.dd_pos
  have hdet : det2 (Amat p) = p.σ * p.β / p.dd := by
    simp only [det2, Amat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    have hd' := hd.ne'
    field_simp
    unfold Par.dd
    ring
  have htr : tr2 (Amat p) = (p.σ + p.κ + p.β * (p.σ + p.φy)) / p.dd := by
    simp only [tr2, Amat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  have hσβ : 0 < p.σ * p.β := mul_pos hp.σ_pos hp.β_pos
  have hlt : p.σ * p.β < p.dd := by
    unfold Par.dd
    nlinarith [mul_nonneg hp.φ_nonneg hp.κ_pos.le, hp.φy_nonneg, hp.σ_pos, hp.β_lt_one]
  rw [hdet, htr]
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos (div_pos hσβ hd), div_lt_one hd]; exact hlt
  · have hT : 0 < (p.σ + p.κ + p.β * (p.σ + p.φy)) / p.dd := by
      have := hp.κ_pos; have := hp.φy_nonneg; have := hp.σ_pos; have := hp.β_pos
      positivity
    rw [abs_of_pos hT, div_lt_iff₀ hd, add_mul, one_mul, div_mul_cancel₀ _ hd.ne']
    have := hp.taylor
    unfold Par.dd
    nlinarith

/-- The entrywise `ℓ¹` size `∑ᵢⱼ |Bᵢⱼ|` of a matrix (a bound for its sup-norm operator norm). -/
def mnorm {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, |B i j|

/-- The entrywise size of a matrix is nonnegative (Woodford (2003), App. A.3, bounds). -/
theorem mnorm_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ mnorm B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `‖Bw‖ ≤ mnorm B ‖w‖` in the sup norm. -/
theorem norm_mulVec_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    ‖B.mulVec w‖ ≤ mnorm B * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mnorm_nonneg B) (norm_nonneg w))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ j, B i j * w j| ≤ ∑ j, |B i j * w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |B i j| * ‖w‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm w j) (abs_nonneg _)
    _ = (∑ j, |B i j|) * ‖w‖ := by rw [Finset.sum_mul]
    _ ≤ mnorm B * ‖w‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
        exact Finset.single_le_sum (f := fun i => ∑ j, |B i j|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/-- Under the Taylor principle `mnorm(Aⁿ) → 0`. -/
theorem tendsto_mnorm_pow (hp : p.Std) : Tendsto (fun n => mnorm (Amat p ^ n)) atTop (𝓝 0) := by
  have h : ∀ i j : Fin 2, Tendsto (fun n => |(Amat p ^ n) i j|) atTop (𝓝 0) := fun i j => by
    simpa using (tendsto_pow_entry (schurStable_Amat hp) i j).abs
  have := tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun i _ =>
    tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun j _ => h i j
  simpa [mnorm] using this

/-- The first power with `mnorm(Aⁿ) ≤ 1/2`. -/
noncomputable def Nhalf (p : Par) : ℕ := sInf {N : ℕ | mnorm (Amat p ^ N) ≤ 1 / 2}

/-- Woodford (2003), Proposition 4.3: under the Taylor principle `mnorm(A^N) ≤ 1/2` at `N = Nhalf`.
-/
theorem mnorm_Nhalf (hp : p.Std) : mnorm (Amat p ^ Nhalf p) ≤ 1 / 2 := by
  have hne : {N : ℕ | mnorm (Amat p ^ N) ≤ 1 / 2}.Nonempty := by
    obtain ⟨N, hN⟩ := ((tendsto_mnorm_pow hp).eventually (ge_mem_nhds
      (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    exact ⟨N, hN N le_rfl⟩
  exact Nat.sInf_mem hne

/-- The constant of the IS–AS block bound: `2 ∑_{k < N} mnorm(Aᵏ)`. -/
noncomputable def CA (p : Par) : ℝ := 2 * ∑ k ∈ Finset.range (Nhalf p), mnorm (Amat p ^ k)

/-- Woodford (2003), App. A.3: the IS–AS block constant is nonnegative. -/
theorem CA_nonneg (p : Par) : 0 ≤ CA p :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => mnorm_nonneg _)

/-- Iterates of `Mv` are additive. -/
theorem iter_add {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (k : ℕ) (h g : X → Fin n → ℝ) :
    (Mv M)^[k] (fun x => h x + g x) = fun x => (Mv M)^[k] h x + (Mv M)^[k] g x := by
  induction k generalizing h g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      Mv_add, ih]

/-- Iterates of `Mv` commute with a constant matrix. -/
theorem iter_mulVec {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (k : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (h : X → Fin n → ℝ) :
    (Mv M)^[k] (fun x => B.mulVec (h x)) = fun x => B.mulVec ((Mv M)^[k] h x) := by
  induction k generalizing h with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Mv_mulVec, ih]

/-- Iterates of a Markov operator keep sup-norm bounds. -/
theorem iter_norm_le {n : ℕ} {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) (k : ℕ)
    {h : X → Fin n → ℝ} {C : ℝ} (hC : 0 ≤ C) (hh : ∀ x, ‖h x‖ ≤ C) (x : X) :
    ‖(Mv M)^[k] h x‖ ≤ C := by
  induction k generalizing h with
  | zero => exact hh x
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (fun x => Mv_norm_le hM hC hh x)

/-- Woodford (2003), (A.13) in Markov form: iterating `u = A M u + b` forward,
`u = ∑_{k<n} Aᵏ Mᵏ b + Aⁿ Mⁿ u`. -/
theorem iterate_eq {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ)
    {u b : X → Fin n → ℝ} (heq : ∀ x, u x = A.mulVec (Mv M u x) + b x) (m : ℕ) (x : X) :
    u x = ∑ k ∈ Finset.range m, (A ^ k).mulVec ((Mv M)^[k] b x) +
      (A ^ m).mulVec ((Mv M)^[m] u x) := by
  have hu : u = fun x => A.mulVec (Mv M u x) + b x := funext heq
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    have h1 : (Mv M)^[m] u x = A.mulVec ((Mv M)^[m + 1] u x) + (Mv M)^[m] b x := by
      conv_lhs => rw [hu]
      rw [iter_add, iter_mulVec, Function.iterate_succ_apply]
    rw [h1, Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ, add_comm]

/-- Woodford (2003), Proposition 4.3 and App. A.3 (**the a-priori bound for the IS–AS block, uniform
over all Markov operators**): if `u = A M u + b` with `u` bounded and `‖b‖ ≤ B`, then
`‖u‖ ≤ C_A B`, with `C_A` depending only on the parameters. -/
theorem twoBlock_bound (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {u b : X → Fin 2 → ℝ} {U0 Bb : ℝ} (hBb : 0 ≤ Bb) (hu0 : ∀ x, ‖u x‖ ≤ U0)
    (hb : ∀ x, ‖b x‖ ≤ Bb) (heq : ∀ x, u x = (Amat p).mulVec (Mv M u x) + b x) (x : X) :
    ‖u x‖ ≤ CA p * Bb := by
  have himp : ∀ U, (∀ x, ‖u x‖ ≤ U) → ∀ x,
      ‖u x‖ ≤ (∑ k ∈ Finset.range (Nhalf p), mnorm (Amat p ^ k)) * Bb + 1 / 2 * U := by
    intro U hU x
    have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU x)
    rw [iterate_eq M (Amat p) heq (Nhalf p) x]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => (norm_mulVec_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_left (iter_norm_le hM k hBb hb x) (mnorm_nonneg _)
    · refine (norm_mulVec_le _ _).trans ?_
      exact mul_le_mul (mnorm_Nhalf hp) (iter_norm_le hM _ hU0 hU x) (norm_nonneg _)
        (by norm_num)
  have h := bound_of_improve (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hu0 himp x
  calc ‖u x‖ ≤ _ := h
    _ = CA p * Bb := by unfold CA; ring

/-! ## The exact equilibrium conditions at a state -/

/-- Woodford (2003), §5 and Ch. 4, (2.7)–(2.8) (**the exact conditions, current-date part**).
With `e = (ν, ĉ, τ̂, q, μ̂ʷ)` the disturbances and `w = (ŷ, π, F̂, K̂)` the endogenous variables at
the current state, the four residuals are `Q(e, w) + E_t[N(e′, w′)]` with
* Euler + rule: `−exp(−(φ_π π + φ_y ŷ + ν + σ(ŷ − ĉ)))`,
* `F`: `e^{F̂} − (1−αβ)e^{f̂}`, `f̂ = (1−σ)ŷ + σĉ + τ̂`,
* `K`: `e^{K̂} − (1−αβ)e^{k̂}`, `k̂ = (1+ω)ŷ − ωq + μ̂ʷ`,
* price index with the reset condition substituted:
  `α(e^{(θ−1)π} − 1) + (1−α)(e^{−(θ−1)(K̂−F̂)/(1+ωθ)} − 1)`. -/
noncomputable def Qmap (p : Par) (q : (Fin 5 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  ![-Real.exp (-(p.φ * q.2 1 + p.φy * q.2 0 + q.1 0 + p.σ * (q.2 0 - q.1 1))),
    Real.exp (q.2 2) - (1 - p.α * p.β) * Real.exp ((1 - p.σ) * q.2 0 + p.σ * q.1 1 + q.1 2),
    Real.exp (q.2 3) - (1 - p.α * p.β) * Real.exp ((1 + p.ω) * q.2 0 - p.ω * q.1 3 + q.1 4),
    p.α * (Real.exp ((p.θ - 1) * q.2 1) - 1) +
      (1 - p.α) * (Real.exp (-((p.θ - 1) * (q.2 3 - q.2 2) / p.c0)) - 1)]

/-- Woodford (2003), §5 and Ch. 4 (**the exact conditions, the part inside `E_t`**), evaluated at
next period's state: `exp(−σ(ŷ′ − ĉ′) − π′)` (Euler), `−αβe^{(θ−1)π′ + F̂′}` (`F`),
`−αβe^{θ(1+ω)π′ + K̂′}` (`K`), `0` (price index). -/
noncomputable def Nmap (p : Par) (q : (Fin 5 → ℝ) × (Fin 4 → ℝ)) : Fin 4 → ℝ :=
  ![Real.exp (-(p.σ * (q.2 0 - q.1 1)) - q.2 1),
    -(p.α * p.β * Real.exp ((p.θ - 1) * q.2 1 + q.2 2)),
    -(p.α * p.β * Real.exp (p.θ * (1 + p.ω) * q.2 1 + q.2 3)), 0]

/-- Woodford (2003), §5 and App. A.3 (**the residual of the Markov equilibrium conditions**) on a
state space `X` with Markov operator `M` (`E_t[h(x_{t+1})] = (Mh)(x_t)`), disturbances `εξ(x)`
and policy functions `z : X → ℝ⁴`: `Φ(ε, z)(x) = Q(εξ(x), z(x)) + M[N(εξ, z)](x)`. -/
noncomputable def Phi (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (ξ : X → Fin 5 → ℝ) (ε : ℝ)
    (z : X → Fin 4 → ℝ) : X → Fin 4 → ℝ :=
  fun x => Qmap p (ε • ξ x, z x) + Mv M (fun x' => Nmap p (ε • ξ x', z x')) x

/-- Woodford (2003), App. A.3: a Markov equilibrium of amplitude `ε` is a zero of `Φ(ε, ·)`. -/
def IsMarkovEqm (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (ξ : X → Fin 5 → ℝ) (ε : ℝ)
    (z : X → Fin 4 → ℝ) : Prop :=
  Phi p M ξ ε z = 0

/-- Woodford (2003), App. A.3: the deterministic steady state (zero inflation, `ŷ = F̂ = K̂ = 0`)
solves the conditions with no disturbances, for every Markov operator. -/
theorem steadyState_eqm {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) (ξ : X → Fin 5 → ℝ) :
    IsMarkovEqm p M ξ 0 0 := by
  have h1 : (fun _ : X => (1 : ℝ)) = fun _ => 1 := rfl
  funext x i
  have hm : ∀ c : ℝ, M (fun _ => c) x = c := fun c => by
    have : (fun _ : X => c) = c • fun _ => (1 : ℝ) := by funext; simp
    rw [this, map_smul, hM.1]; simp
  fin_cases i <;>
    simp [Phi, Mv, Qmap, Nmap, hm]

/-- The linearisation of `Q` in `w` at the steady state (`DQ`). -/
noncomputable def DQ0 (p : Par) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(p.σ + p.φy) * v 0 + p.φ * v 1,
    v 2 - (1 - p.α * p.β) * (1 - p.σ) * v 0,
    v 3 - (1 - p.α * p.β) * (1 + p.ω) * v 0,
    p.α * (p.θ - 1) * v 1 - (1 - p.α) * (p.θ - 1) * (v 3 - v 2) / p.c0]

/-- The linearisation of `N` in `w` at the steady state (`DN`). -/
noncomputable def DN0 (p : Par) (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![-(p.σ * v 0 + v 1), -(p.α * p.β * ((p.θ - 1) * v 1 + v 2)),
    -(p.α * p.β * (p.θ * (1 + p.ω) * v 1 + v 3)), 0]

/-- Woodford (2003), App. A.3, (A.12) in Markov form: the linearised operator
`(L v)(x) = DQ v(x) + M[DN v](x)`. -/
noncomputable def Lop (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v : X → Fin 4 → ℝ) :
    X → Fin 4 → ℝ :=
  fun x => DQ0 p (v x) + Mv M (fun x' => DN0 p (v x')) x

/-- Linearity of `M` on a two-term combination. -/
theorem M_lin (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (a b : ℝ) (f g : X → ℝ) (x : X) :
    M (fun x' => a * f x' + b * g x') x = a * M f x + b * M g x := by
  have : (fun x' => a * f x' + b * g x') = a • f + b • g := by funext; simp
  rw [this, map_add, map_smul, map_smul]
  simp

/-- Woodford (2003), (A.12): the four components of the linearised operator. -/
theorem Lop_apply (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v : X → Fin 4 → ℝ) (x : X) :
    Lop p M v x 0 = (p.σ + p.φy) * v x 0 + p.φ * v x 1 - p.σ * M (fun x' => v x' 0) x -
        M (fun x' => v x' 1) x ∧
    Lop p M v x 1 = v x 2 - (1 - p.α * p.β) * (1 - p.σ) * v x 0 -
        p.α * p.β * (p.θ - 1) * M (fun x' => v x' 1) x - p.α * p.β * M (fun x' => v x' 2) x ∧
    Lop p M v x 2 = v x 3 - (1 - p.α * p.β) * (1 + p.ω) * v x 0 -
        p.α * p.β * (p.θ * (1 + p.ω)) * M (fun x' => v x' 1) x -
        p.α * p.β * M (fun x' => v x' 3) x ∧
    Lop p M v x 3 = p.α * (p.θ - 1) * v x 1 - (1 - p.α) * (p.θ - 1) * (v x 3 - v x 2) / p.c0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := M_lin M (-p.σ) (-1) (fun x' => v x' 0) (fun x' => v x' 1) x
    have e : (fun x' => -p.σ * v x' 0 + -1 * v x' 1) = fun x' => -(p.σ * v x' 0 + v x' 1) := by
      funext; ring
    rw [e] at h
    simp only [Lop, DN0, DQ0, Mv, Pi.add_apply, Matrix.cons_val_zero]
    rw [h]; ring
  · have h := M_lin M (-(p.α * p.β * (p.θ - 1))) (-(p.α * p.β)) (fun x' => v x' 1)
      (fun x' => v x' 2) x
    have e : (fun x' => -(p.α * p.β * (p.θ - 1)) * v x' 1 + -(p.α * p.β) * v x' 2) =
        fun x' => -(p.α * p.β * ((p.θ - 1) * v x' 1 + v x' 2)) := by funext; ring
    rw [e] at h
    simp only [Lop, DN0, DQ0, Mv, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h]; ring
  · have h := M_lin M (-(p.α * p.β * (p.θ * (1 + p.ω)))) (-(p.α * p.β)) (fun x' => v x' 1)
      (fun x' => v x' 3) x
    have e : (fun x' => -(p.α * p.β * (p.θ * (1 + p.ω))) * v x' 1 + -(p.α * p.β) * v x' 3) =
        fun x' => -(p.α * p.β * (p.θ * (1 + p.ω) * v x' 1 + v x' 3)) := by funext; ring
    rw [e] at h
    simp only [Lop, DN0, DQ0, Mv, Pi.add_apply]
    simp only [show (2 : Fin 4) = Fin.succ 1 from rfl, Matrix.cons_val_succ, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [h]; ring
  · have h0 : M (fun _ => (0 : ℝ)) x = 0 := by
      have : (fun _ : X => (0 : ℝ)) = 0 := rfl
      rw [this, map_zero]; rfl
    simp only [Lop, DN0, DQ0, Mv, Pi.add_apply]
    simp only [show (3 : Fin 4) = Fin.succ (Fin.succ 1) from rfl, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h0, add_zero]

/-! ## The a-priori bound, uniform over Markov operators -/

/-- Constant: the bound `|s₁| ≤ S₁ a` of the NKPC residual. -/
noncomputable def S1c (p : Par) : ℝ := (2 + p.k3 + p.α * p.β * p.k3) / p.cR

/-- Constant: the bound of the forcing of the IS–AS block. -/
noncomputable def Bc (p : Par) : ℝ := (1 + p.φ * S1c p + p.κ + (p.σ + p.φy) * S1c p) / p.dd

/-- Constant: the bound of `ŷ` and `π`. -/
noncomputable def Uc (p : Par) : ℝ := CA p * Bc p

/-- Constant: the bound of `F̂`. -/
noncomputable def Fc (p : Par) : ℝ :=
  (1 + ((1 - p.α * p.β) * |1 - p.σ| + p.α * p.β * (p.θ - 1)) * Uc p) / (1 - p.α * p.β)

/-- Constant: the bound of `K̂`. -/
noncomputable def Kc (p : Par) : ℝ := Fc p + p.cR * Uc p + p.k3

/-- Woodford (2003), App. A.3: the constant of the a-priori bound `‖v‖ ≤ K‖Lv‖`. -/
noncomputable def Kap (p : Par) : ℝ := Uc p + Fc p + Kc p

/-- Woodford (2003), §5: `(1+ωθ)/((1−α)(θ−1)) > 0`. -/
theorem Par.Std.k3_pos (hp : p.Std) : 0 < p.k3 := by
  unfold Par.k3
  have := hp.c0_pos; have : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  have : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  positivity

/-- Woodford (2003), App. A.3: the NKPC-residual constant is nonnegative. -/
theorem S1c_nonneg (hp : p.Std) : 0 ≤ S1c p := by
  unfold S1c; have := hp.k3_pos; have := hp.cR_pos; have := hp.ab_pos; positivity

/-- Woodford (2003), App. A.3: the forcing constant is nonnegative. -/
theorem Bc_nonneg (hp : p.Std) : 0 ≤ Bc p := by
  unfold Bc; have := S1c_nonneg hp; have := hp.dd_pos; have := hp.κ_pos
  have := hp.φ_nonneg; have := hp.σ_pos; have := hp.φy_nonneg; positivity

/-- Woodford (2003), App. A.3: the bound constant for `ŷ`, `π` is nonnegative. -/
theorem Uc_nonneg (hp : p.Std) : 0 ≤ Uc p := mul_nonneg (CA_nonneg p) (Bc_nonneg hp)

/-- Woodford (2003), App. A.3: the bound constant for `F̂` is nonnegative. -/
theorem Fc_nonneg (hp : p.Std) : 0 ≤ Fc p := by
  unfold Fc
  have := Uc_nonneg hp; have := hp.ab_pos; have : 0 < 1 - p.α * p.β := by linarith [hp.ab_lt_one]
  have : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  positivity

/-- Woodford (2003), App. A.3: the bound constant for `K̂` is nonnegative. -/
theorem Kc_nonneg (hp : p.Std) : 0 ≤ Kc p := by
  unfold Kc; have := Fc_nonneg hp; have := Uc_nonneg hp; have := hp.cR_pos
  have := hp.k3_pos; positivity

/-- Woodford (2003), App. A.3, (A.12)–(A.13) and Proposition 4.3 (**the a-priori bound, uniform
over state spaces and Markov operators**): under the Taylor principle, every bounded `v` satisfies
`‖v(x)‖ ≤ K · sup ‖(Lv)‖` with `K = Kap p` depending only on the parameters. In particular the
linearised operator is injective on bounded functions of any Markov state. -/
theorem apriori (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {v : X → Fin 4 → ℝ} {V0 a : ℝ} (hv0 : ∀ x, ‖v x‖ ≤ V0)
    (ha : ∀ x, ‖Lop p M v x‖ ≤ a) (x : X) : ‖v x‖ ≤ Kap p * a := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha x)
  have hr : ∀ i x, |Lop p M v x i| ≤ a := fun i x => by
    have := norm_le_pi_norm (Lop p M v x) i
    rw [Real.norm_eq_abs] at this
    exact this.trans (ha x)
  have hvc : ∀ i x, |v x i| ≤ V0 := fun i x => by
    have := norm_le_pi_norm (v x) i
    rw [Real.norm_eq_abs] at this
    exact this.trans (hv0 x)
  set r : Fin 4 → X → ℝ := fun i x => Lop p M v x i with hrdef
  set y : X → ℝ := fun x => v x 0 with hy
  set pp : X → ℝ := fun x => v x 1 with hpp
  set F : X → ℝ := fun x => v x 2 with hF
  set K : X → ℝ := fun x => v x 3 with hK
  have hcomp := fun x => Lop_apply (p := p) M v x
  have hc0 := hp.c0_pos
  have h1α : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  have hθ1 : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  -- the reset gap
  have hG : ∀ x, K x - F x = p.cR * pp x - p.k3 * r 3 x := fun x => by
    have h3 := (hcomp x).2.2.2
    simp only [hrdef, hK, hF, hpp]
    rw [h3]
    unfold Par.cR Par.k3
    field_simp
    ring
  have hMG : ∀ x, M K x - M F x = p.cR * M pp x - p.k3 * M (r 3) x := fun x => by
    have e1 : (fun x => K x - F x) = fun x => p.cR * pp x + -p.k3 * r 3 x := by
      funext x; rw [hG x]; ring
    have e2 := M_lin M 1 (-1) K F x
    have e3 := M_lin M p.cR (-p.k3) pp (r 3) x
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e2
    rw [← e2, e1, e3]; ring
  -- the NKPC residual
  set s1 : X → ℝ := fun x =>
    (r 2 x - r 1 x + p.k3 * r 3 x - p.α * p.β * p.k3 * M (r 3) x) / p.cR with hs1
  have hNK : ∀ x, pp x - p.β * M pp x - p.κ * y x = s1 x := fun x => by
    have h1 := (hcomp x).2.1
    have h2 := (hcomp x).2.2.1
    have hk' : p.κ * p.cR = (1 - p.α * p.β) * (p.ω + p.σ) := by
      rw [hp.κ_eq]; field_simp [hp.cR_pos.ne']
    have hab := hp.ab_c
    have hcR := hp.cR_pos.ne'
    have hGx := hG x
    have hMGx := hMG x
    simp only [hs1, hrdef, hpp, hy, hK, hF] at hGx hMGx ⊢
    rw [h1, h2, eq_div_iff hcR]
    unfold Par.c0 at hab
    linear_combination (-1 : ℝ) * hGx + p.α * p.β * hMGx - v x 0 * hk' +
      M (fun x' => v x' 1) x * hab
  have hS1 : ∀ x, |s1 x| ≤ S1c p * a := fun x => by
    have hm3 : |M (r 3) x| ≤ a := hM.2 _ a (fun x' => hr 3 x') x
    have hk3 := hp.k3_pos
    have hab := hp.ab_pos
    simp only [hs1, S1c]
    rw [abs_div, abs_of_pos hp.cR_pos, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp.cR_pos]
    calc |r 2 x - r 1 x + p.k3 * r 3 x - p.α * p.β * p.k3 * M (r 3) x|
        ≤ |r 2 x| + |r 1 x| + p.k3 * |r 3 x| + p.α * p.β * p.k3 * |M (r 3) x| := by
          have e1 := abs_sub (r 2 x - r 1 x + p.k3 * r 3 x) (p.α * p.β * p.k3 * M (r 3) x)
          have e2 := abs_add_le (r 2 x - r 1 x) (p.k3 * r 3 x)
          have e3 := abs_sub (r 2 x) (r 1 x)
          rw [abs_mul (p.α * p.β * p.k3), abs_of_pos (by positivity : 0 < p.α * p.β * p.k3),
            abs_mul, abs_of_pos hk3] at *
          linarith
      _ ≤ a + a + p.k3 * a + p.α * p.β * p.k3 * a := by
          gcongr
          · exact hr 2 x
          · exact hr 1 x
          · exact hr 3 x
      _ = (2 + p.k3 + p.α * p.β * p.k3) * a := by ring
  -- the IS–AS block
  set u : X → Fin 2 → ℝ := fun x => ![y x, pp x] with hu
  set b : X → Fin 2 → ℝ := fun x => ![(r 0 x - p.φ * s1 x) / p.dd,
    (p.κ * r 0 x + (p.σ + p.φy) * s1 x) / p.dd] with hb
  have hMu : ∀ x, Mv M u x = ![M y x, M pp x] := fun x => by
    funext i; fin_cases i <;> rfl
  have hd := hp.dd_pos
  have heq : ∀ x, u x = (Amat p).mulVec (Mv M u x) + b x := fun x => by
    rw [hMu]
    have h0 := (hcomp x).1
    have hnk := hNK x
    simp only [hy, hpp] at h0 hnk
    funext i
    fin_cases i
    · simp only [hu, hb, Amat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, hrdef, Fin.zero_eta, Fin.isValue]
      rw [h0, ← hnk]
      field_simp
      unfold Par.dd
      ring
    · simp only [hu, hb, Amat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one, hrdef, Fin.mk_one, Fin.isValue]
      rw [h0, ← hnk]
      field_simp
      unfold Par.dd
      ring
  have hu0 : ∀ x, ‖u x‖ ≤ V0 := fun x => by
    have hV0 : 0 ≤ V0 := (abs_nonneg _).trans (hvc 0 x)
    refine (pi_norm_le_iff_of_nonneg hV0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    fin_cases i
    · exact hvc 0 x
    · exact hvc 1 x
  have hbb : ∀ x, ‖b x‖ ≤ Bc p * a := fun x => by
    have hBa : 0 ≤ Bc p * a := mul_nonneg (Bc_nonneg hp) ha0
    have h0 := hr 0 x
    have hs := hS1 x
    have hS1n := S1c_nonneg hp
    have hκ := hp.κ_pos
    have hφ := hp.φ_nonneg
    have hσφ : 0 ≤ p.σ + p.φy := by linarith [hp.σ_pos, hp.φy_nonneg]
    refine (pi_norm_le_iff_of_nonneg hBa).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have hnum : ∀ c1 c2 : ℝ, |c1| ≤ 1 + p.κ → |c2| ≤ p.φ + (p.σ + p.φy) →
        |c1 * r 0 x + c2 * s1 x| / p.dd ≤ Bc p * a := fun c1 c2 hc1 hc2 => by
      rw [div_le_iff₀ hd]
      unfold Bc
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hd.ne']
      calc |c1 * r 0 x + c2 * s1 x| ≤ |c1| * |r 0 x| + |c2| * |s1 x| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ (1 + p.κ) * a + (p.φ + (p.σ + p.φy)) * (S1c p * a) := by
            gcongr
        _ = (1 + p.φ * S1c p + p.κ + (p.σ + p.φy) * S1c p) * a := by ring
    fin_cases i
    · have := hnum 1 (-p.φ) (by rw [abs_one]; linarith)
        (by rw [abs_neg, abs_of_nonneg hφ]; linarith)
      simp only [hb, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
      rw [abs_div, abs_of_pos hd]
      convert this using 3; ring
    · have := hnum p.κ (p.σ + p.φy) (by rw [abs_of_pos hκ]; linarith)
        (by rw [abs_of_nonneg hσφ]; linarith)
      simp only [hb, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue]
      rw [abs_div, abs_of_pos hd]
      exact this
  have hU : ∀ x, ‖u x‖ ≤ Uc p * a := fun x => by
    have := twoBlock_bound hp hM (mul_nonneg (Bc_nonneg hp) ha0) hu0 hbb heq x
    unfold Uc; rw [mul_assoc]; exact this
  have hyb : ∀ x, |y x| ≤ Uc p * a := fun x => by
    have := norm_le_pi_norm (u x) 0
    simp only [hu, Matrix.cons_val_zero, Real.norm_eq_abs] at this
    exact this.trans (hU x)
  have hpb : ∀ x, |pp x| ≤ Uc p * a := fun x => by
    have := norm_le_pi_norm (u x) 1
    simp only [hu, Matrix.cons_val_one, Real.norm_eq_abs] at this
    exact this.trans (hU x)
  -- the auxiliary sum `F`
  have hab0 := hp.ab_pos
  have hab1 := hp.ab_lt_one
  have hFb : ∀ x, |F x| ≤ Fc p * a := by
    intro x
    have himp : ∀ U, (∀ x, ‖F x‖ ≤ U) → ∀ x, ‖F x‖ ≤
        (1 + ((1 - p.α * p.β) * |1 - p.σ| + p.α * p.β * (p.θ - 1)) * Uc p) * a +
          p.α * p.β * U := by
      intro U hU x
      have hU' : ∀ x, |F x| ≤ U := fun x => by simpa using hU x
      have h1 := (hcomp x).2.1
      have hmF : |M F x| ≤ U := hM.2 _ U hU' x
      have hmp : |M pp x| ≤ Uc p * a := hM.2 _ _ hpb x
      have hFx : F x = r 1 x + (1 - p.α * p.β) * (1 - p.σ) * y x +
          p.α * p.β * (p.θ - 1) * M pp x + p.α * p.β * M F x := by
        simp only [hrdef, hF, hy, hpp]; rw [h1]; ring
      rw [Real.norm_eq_abs, hFx]
      have e1 : |(1 - p.α * p.β) * (1 - p.σ) * y x| ≤ (1 - p.α * p.β) * |1 - p.σ| * (Uc p * a) := by
        rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 - p.α * p.β)]
        exact mul_le_mul_of_nonneg_left (hyb x) (by positivity)
      have e2 : |p.α * p.β * (p.θ - 1) * M pp x| ≤ p.α * p.β * (p.θ - 1) * (Uc p * a) := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < p.α * p.β * (p.θ - 1))]
        exact mul_le_mul_of_nonneg_left hmp (by positivity)
      have e3 : |p.α * p.β * M F x| ≤ p.α * p.β * U := by
        rw [abs_mul, abs_of_pos hab0]
        exact mul_le_mul_of_nonneg_left hmF hab0.le
      have e4 := hr 1 x
      have t1 := abs_add_le (r 1 x + (1 - p.α * p.β) * (1 - p.σ) * y x +
        p.α * p.β * (p.θ - 1) * M pp x) (p.α * p.β * M F x)
      have t2 := abs_add_le (r 1 x + (1 - p.α * p.β) * (1 - p.σ) * y x)
        (p.α * p.β * (p.θ - 1) * M pp x)
      have t3 := abs_add_le (r 1 x) ((1 - p.α * p.β) * (1 - p.σ) * y x)
      nlinarith
    have h := bound_of_improve hab0.le hab1 (fun x => by
      rw [Real.norm_eq_abs]; exact hvc 2 x) himp x
    rw [Real.norm_eq_abs] at h
    refine h.trans (le_of_eq ?_)
    unfold Fc
    have : 1 - p.α * p.β ≠ 0 := by linarith
    field_simp
  have hKb : ∀ x, |K x| ≤ Kc p * a := fun x => by
    have hKx : K x = F x + (p.cR * pp x - p.k3 * r 3 x) := by rw [← hG x]; ring
    rw [hKx]
    have e1 := abs_add_le (F x) (p.cR * pp x - p.k3 * r 3 x)
    have e2 := abs_sub (p.cR * pp x) (p.k3 * r 3 x)
    rw [abs_mul, abs_of_pos hp.cR_pos, abs_mul (p.k3), abs_of_pos hp.k3_pos] at e2
    have := mul_le_mul_of_nonneg_left (hpb x) hp.cR_pos.le
    have := mul_le_mul_of_nonneg_left (hr 3 x) hp.k3_pos.le
    have := hFb x
    unfold Kc
    nlinarith
  have hK0 : 0 ≤ Kap p * a := mul_nonneg (by
    unfold Kap; have := Uc_nonneg hp; have := Fc_nonneg hp; have := Kc_nonneg hp; linarith) ha0
  refine (pi_norm_le_iff_of_nonneg hK0).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hUa := mul_nonneg (Uc_nonneg hp) ha0
  have hFa := mul_nonneg (Fc_nonneg hp) ha0
  have hKa := mul_nonneg (Kc_nonneg hp) ha0
  unfold Kap
  fin_cases i
  · have := hyb x; simp only [hy] at this; simp only [Fin.zero_eta, Fin.isValue]; nlinarith
  · have := hpb x; simp only [hpp] at this; simp only [Fin.mk_one, Fin.isValue]; nlinarith
  · have := hFb x; simp only [hF] at this
    simp only [Fin.reduceFinMk, Fin.isValue]; nlinarith
  · have := hKb x; simp only [hK] at this
    simp only [Fin.reduceFinMk, Fin.isValue]; nlinarith

/-- Woodford (2003), App. A.3: under the Taylor principle the linearised operator is injective on
bounded functions of any Markov state. -/
theorem Lop_injective (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {v : X → Fin 4 → ℝ} {V0 : ℝ} (hv0 : ∀ x, ‖v x‖ ≤ V0) (h0 : Lop p M v = 0) : v = 0 := by
  funext x
  have := apriori hp hM hv0 (a := 0) (fun x => by rw [h0]; simp) x
  rw [mul_zero] at this
  exact norm_le_zero_iff.1 this

/-! ## Smoothness and the derivative of the residual map -/

/-- Woodford (2003), App. A.3: the current-date part `Q` of the conditions is `C^∞`. -/
theorem contDiff_Qmap {n : WithTop ℕ∞} : ContDiff ℝ n (Qmap p) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Qmap, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop

/-- Woodford (2003), App. A.3: the part `N` inside `E_t` is `C^∞`. -/
theorem contDiff_Nmap {n : WithTop ℕ∞} : ContDiff ℝ n (Nmap p) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Nmap, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop

/-- `t ↦ d·exp(tc)` has derivative `dc` at `0`. -/
theorem hasDerivAt_exp_line (c d : ℝ) :
    HasDerivAt (fun t : ℝ => d * Real.exp (t * c)) (d * c) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const c).exp.const_mul d
  simpa using h

/-- Woodford (2003), App. A.3: the derivative of `Q` along the line `t ↦ (0, tw)` at the steady
state is `DQ w`. -/
theorem hasDerivAt_Qmap_line (w : Fin 4 → ℝ) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => Qmap p (0, t • w) i) (DQ0 p w i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := hasDerivAt_exp_line (-(p.φ * w 1 + p.φy * w 0 + p.σ * w 0)) (-1)
    refine (h.congr_deriv (by simp [DQ0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring_nf
  · have h := (hasDerivAt_exp_line (w 2) 1).sub
      (hasDerivAt_exp_line ((1 - p.σ) * w 0) (1 - p.α * p.β))
    refine (h.congr_deriv (by simp [DQ0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := (hasDerivAt_exp_line (w 3) 1).sub
      (hasDerivAt_exp_line ((1 + p.ω) * w 0) (1 - p.α * p.β))
    refine (h.congr_deriv (by simp [DQ0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := ((hasDerivAt_exp_line ((p.θ - 1) * w 1) p.α).sub_const p.α).add
      ((hasDerivAt_exp_line (-((p.θ - 1) * (w 3 - w 2) / p.c0)) (1 - p.α)).sub_const (1 - p.α))
    refine (h.congr_deriv (by simp [DQ0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring_nf

/-- Woodford (2003), App. A.3: the derivative of `N` along the line `t ↦ (0, tw)` at the steady
state is `DN w`. -/
theorem hasDerivAt_Nmap_line (w : Fin 4 → ℝ) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => Nmap p (0, t • w) i) (DN0 p w i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := hasDerivAt_exp_line (-(p.σ * w 0) - w 1) 1
    refine (h.congr_deriv (by simp [DN0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring_nf
  · have h := hasDerivAt_exp_line ((p.θ - 1) * w 1 + w 2) (-(p.α * p.β))
    refine (h.congr_deriv (by simp [DN0])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · have h := hasDerivAt_exp_line (p.θ * (1 + p.ω) * w 1 + w 3) (-(p.α * p.β))
    refine (h.congr_deriv (by simp [DN0])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · simp only [Nmap, DN0, Matrix.cons_val, Fin.isValue]
    exact hasDerivAt_const _ _

/-! ## Existence and local uniqueness on a finite Markov chain (the implicit function theorem) -/

variable {S : Type*} [Fintype S]

/-- Woodford (2003), App. A.3: the residual map on a finite chain as a function of
`(ε, z) ∈ ℝ × (S → ℝ⁴)`. -/
noncomputable def PhiS (p : Par) (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ)
    (q : ℝ × (S → Fin 4 → ℝ)) : S → Fin 4 → ℝ :=
  Phi p (chainOp P) ξ q.1 q.2

/-- Woodford (2003), App. A.3: the residual on a finite chain, componentwise. -/
theorem PhiS_apply (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) (q : ℝ × (S → Fin 4 → ℝ)) (s : S)
    (i : Fin 4) : PhiS p P ξ q s i = Qmap p (q.1 • ξ s, q.2 s) i +
      ∑ s', P s s' * Nmap p (q.1 • ξ s', q.2 s') i := rfl

/-- Woodford (2003), App. A.3: the residual map is `C^∞` on `ℝ × (S → ℝ⁴)`. -/
theorem contDiff_PhiS {n : WithTop ℕ∞} (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) :
    ContDiff ℝ n (PhiS p P ξ) := by
  refine contDiff_pi.2 fun s => contDiff_pi.2 fun i => ?_
  have hQ : ContDiff ℝ n (fun q : ℝ × (S → Fin 4 → ℝ) => Qmap p (q.1 • ξ s, q.2 s) i) :=
    (contDiff_apply ℝ ℝ i).comp (contDiff_Qmap.comp (by fun_prop))
  have hN : ∀ s', ContDiff ℝ n
      (fun q : ℝ × (S → Fin 4 → ℝ) => P s s' * Nmap p (q.1 • ξ s', q.2 s') i) := fun s' =>
    contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp (contDiff_Nmap.comp (by fun_prop)))
  exact hQ.add (ContDiff.sum fun s' _ => hN s')

/-- Woodford (2003), App. A.3: the augmented map `(ε, z) ↦ (ε, Φ(ε, z))` to which the inverse
function theorem is applied. -/
noncomputable def bigMap (p : Par) (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ)
    (q : ℝ × (S → Fin 4 → ℝ)) : ℝ × (S → Fin 4 → ℝ) :=
  (q.1, PhiS p P ξ q)

/-- Woodford (2003), App. A.3: the augmented map is `C^∞`. -/
theorem contDiff_bigMap {n : WithTop ℕ∞} (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) :
    ContDiff ℝ n (bigMap p P ξ) :=
  contDiff_fst.prodMk (contDiff_PhiS P ξ)

/-- Woodford (2003), App. A.3: the derivative of the residual along `t ↦ (0, tv)` at the steady
state is the linearised operator `Lv`. -/
theorem hasDerivAt_PhiS_line (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) (v : S → Fin 4 → ℝ) :
    HasDerivAt (fun t : ℝ => PhiS p P ξ (0, t • v)) (Lop p (chainOp P) v) 0 := by
  rw [hasDerivAt_pi]
  intro s
  rw [hasDerivAt_pi]
  intro i
  have hQ := hasDerivAt_Qmap_line (p := p) (v s) i
  have hN : ∀ s' ∈ (Finset.univ : Finset S), HasDerivAt
      (fun t : ℝ => P s s' * Nmap p (0, t • v s') i) (P s s' * DN0 p (v s') i) 0 :=
    fun s' _ => (hasDerivAt_Nmap_line (v s') i).const_mul (P s s')
  have h := hQ.add (HasDerivAt.sum hN)
  convert h using 1
  · funext t
    simp only [PhiS_apply, zero_smul, Pi.smul_apply, Pi.add_apply, Finset.sum_apply]
  · simp only [Lop, Mv, chainOp, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]

/-- Woodford (2003), App. A.3: the partial derivative of `Φ` in `z` at the steady state is `L`. -/
theorem fderiv_PhiS_apply (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) (v : S → Fin 4 → ℝ) :
    fderiv ℝ (PhiS p P ξ) (0, 0) (0, v) = Lop p (chainOp P) v := by
  have hd : HasFDerivAt (PhiS p P ξ) (fderiv ℝ (PhiS p P ξ) (0, 0)) (0, 0) :=
    ((contDiff_PhiS (n := 1) P ξ).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : ℝ), t • v)) ((0 : ℝ), v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_PhiS_line P ξ v)

/-- Woodford (2003), App. A.3 and Proposition 4.3: under the Taylor principle the derivative of
the augmented map at the steady state is injective. -/
theorem fderiv_bigMap_injective (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 5 → ℝ) : Function.Injective (fderiv ℝ (bigMap p P ξ) (0, 0)) := by
  have hd0 : HasFDerivAt (PhiS p P ξ) (fderiv ℝ (PhiS p P ξ) (0, 0)) (0, 0) :=
    ((contDiff_PhiS (n := 1) P ξ).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hd : HasFDerivAt (bigMap p P ξ)
      ((ContinuousLinearMap.fst ℝ ℝ (S → Fin 4 → ℝ)).prod (fderiv ℝ (PhiS p P ξ) (0, 0)))
      (0, 0) := hasFDerivAt_fst.prodMk hd0
  rw [hd.fderiv, injective_iff_map_eq_zero]
  rintro ⟨τ, v⟩ hq
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', Prod.mk_eq_zero] at hq
  obtain ⟨hτ, hv⟩ := hq
  subst hτ
  rw [fderiv_PhiS_apply] at hv
  have := Lop_injective hp (chainOp_isMarkov hP) (V0 := ‖v‖) (fun s => norm_le_pi_norm v s) hv
  rw [this]
  rfl

/-- The derivative of the augmented map at the steady state as a continuous linear equivalence
(injective endomorphism of a finite-dimensional space). -/
noncomputable def derivEquiv (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 5 → ℝ) : (ℝ × (S → Fin 4 → ℝ)) ≃L[ℝ] (ℝ × (S → Fin 4 → ℝ)) :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ (bigMap p P ξ) (0, 0) :
    (ℝ × (S → Fin 4 → ℝ)) →ₗ[ℝ] (ℝ × (S → Fin 4 → ℝ)))
    (fderiv_bigMap_injective hp hP ξ)).toContinuousLinearEquiv

/-- Woodford (2003), App. A.3: the augmented map has the invertible derivative `derivEquiv`. -/
theorem hasFDerivAt_bigMap (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 5 → ℝ) :
    HasFDerivAt (bigMap p P ξ) (derivEquiv hp hP ξ : (ℝ × (S → Fin 4 → ℝ)) →L[ℝ] _) (0, 0) := by
  have hd : HasFDerivAt (bigMap p P ξ) (fderiv ℝ (bigMap p P ξ) (0, 0)) (0, 0) :=
    ((contDiff_bigMap (n := 1) P ξ).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  convert hd using 1
  exact ContinuousLinearMap.ext fun q => rfl

/-- Woodford (2003), App. A.3: the steady state is a zero of the augmented map. -/
theorem bigMap_zero {P : S → S → ℝ} (hP : Stochastic P) (ξ : S → Fin 5 → ℝ) :
    bigMap p P ξ (0, 0) = (0, 0) := by
  have h := steadyState_eqm (p := p) (chainOp_isMarkov hP) ξ
  simp only [bigMap, PhiS]
  rw [show Phi p (chainOp P) ξ 0 0 = 0 from h]

/-- Woodford (2003), Ch. 6, §1 (the one-parameter family of economies) and App. A.3, with the
Taylor principle (Proposition 4.3) — **EXISTENCE AND LOCAL UNIQUENESS OF A MARKOV EQUILIBRIUM OF
THE EXACT NONLINEAR NEW KEYNESIAN MODEL**. For a finite Markov chain `(S, P)`, any bounded
disturbance pattern `ξ` and the parameters satisfying the Taylor principle, there are `r, δ > 0`
and a family `ε ↦ z_ε` of policy functions `S → ℝ⁴` (`ŷ, π, F̂, K̂` as functions of the exogenous
state) such that
* `z₀ = 0`: the deterministic steady state is the base point;
* `ε ↦ z_ε` is `C²` at `0` (in the sup norm, i.e. uniformly in the state);
* for `|ε| < δ`, `z_ε` is a Markov equilibrium with `‖z_ε‖ < r`;
* it is the ONLY Markov equilibrium in the ball `‖z‖ < r`, for each `|ε| < δ`. -/
theorem markov_equilibrium (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 5 → ℝ) :
    ∃ r > 0, ∃ δ > 0, ∃ z : ℝ → S → Fin 4 → ℝ, z 0 = 0 ∧ ContDiffAt ℝ 2 z 0 ∧
      (∀ ε, |ε| < δ → IsMarkovEqm p (chainOp P) ξ ε (z ε) ∧ ‖z ε‖ < r) ∧
      ∀ ε w, |ε| < δ → ‖w‖ < r → IsMarkovEqm p (chainOp P) ξ ε w → w = z ε := by
  set f := bigMap p P ξ with hfdef
  have hf : ContDiffAt ℝ 2 f (0, 0) := (contDiff_bigMap P ξ).contDiffAt
  have hf' := hasFDerivAt_bigMap hp hP ξ
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by decide
  set φh := hf.toOpenPartialHomeomorph f hf' hn with hφh
  have h00 : f (0, 0) = (0, 0) := bigMap_zero hP ξ
  have hsrc : ((0 : ℝ), (0 : S → Fin 4 → ℝ)) ∈ φh.source :=
    hf.mem_toOpenPartialHomeomorph_source hf' hn
  have htgt : ((0 : ℝ), (0 : S → Fin 4 → ℝ)) ∈ φh.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target hf' hn
    rwa [h00] at this
  have hcoe : (φh : ℝ × (S → Fin 4 → ℝ) → ℝ × (S → Fin 4 → ℝ)) = f := rfl
  have hsymm0 : φh.symm (0, 0) = (0, 0) := by
    have := φh.left_inv hsrc
    rwa [hcoe, h00] at this
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 φh.open_source (0, 0) hsrc
  have hline : Continuous fun ε : ℝ => (ε, (0 : S → Fin 4 → ℝ)) :=
    continuous_id.prodMk continuous_const
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), (ε, (0 : S → Fin 4 → ℝ)) ∈ φh.target :=
    hline.continuousAt.preimage_mem_nhds (φh.open_target.mem_nhds htgt)
  have hcont : ContinuousAt (fun ε : ℝ => φh.symm (ε, 0)) 0 := by
    have h1 : ContinuousAt φh.symm ((fun ε : ℝ => (ε, (0 : S → Fin 4 → ℝ))) 0) :=
      φh.continuousAt_symm htgt
    exact ContinuousAt.comp (f := fun ε : ℝ => (ε, (0 : S → Fin 4 → ℝ))) h1 hline.continuousAt
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), φh.symm (ε, 0) ∈ Metric.ball (0, 0) r := by
    have := hcont.tendsto
    rw [hsymm0] at this
    exact this (Metric.ball_mem_nhds _ hr)
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
  refine ⟨r, hr, min δ r, lt_min hδ hr, fun ε => (φh.symm (ε, 0)).2, ?_, ?_, ?_, ?_⟩
  · simp [hsymm0]
  · have hloc := hf.to_localInverse hf' hn
    rw [h00] at hloc
    have hl2 : ContDiffAt ℝ 2 (fun ε : ℝ => (ε, (0 : S → Fin 4 → ℝ))) 0 := by fun_prop
    have hcomp := hloc.comp (0 : ℝ) hl2
    exact contDiffAt_snd.comp (0 : ℝ) hcomp
  · intro ε hε
    have hεδ : dist ε 0 < δ := by
      rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hε (min_le_left _ _)
    obtain ⟨ht, hb⟩ := hδev hεδ
    have hri := φh.right_inv ht
    rw [hcoe] at hri
    set q := φh.symm (ε, 0) with hq
    have h1 : q.1 = ε := congrArg Prod.fst hri
    have h2 : PhiS p P ξ q = 0 := congrArg Prod.snd hri
    refine ⟨?_, ?_⟩
    · change Phi p (chainOp P) ξ ε q.2 = 0
      rw [← h1]; exact h2
    · rw [Metric.mem_ball] at hb
      have hb' : dist q 0 < r := hb
      rw [dist_zero_right] at hb'
      exact lt_of_le_of_lt (norm_snd_le q) hb'
  · intro ε w hε hw heq
    have hεδ : dist ε 0 < δ := by
      rw [Real.dist_eq, sub_zero]; exact lt_of_lt_of_le hε (min_le_left _ _)
    obtain ⟨ht, _⟩ := hδev hεδ
    have hεr : |ε| < r := lt_of_lt_of_le hε (min_le_right _ _)
    have hin : (ε, w) ∈ φh.source := hball (by
      rw [Metric.mem_ball]
      change dist (ε, w) 0 < r
      rw [dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs]
      exact ⟨hεr, hw⟩)
    have hq := φh.map_target ht
    have hfw : φh (ε, w) = (ε, 0) := by
      rw [hcoe]
      simp only [hfdef, bigMap, PhiS]
      rw [show Phi p (chainOp P) ξ ε w = 0 from heq]
    have hfq : φh (φh.symm (ε, 0)) = (ε, 0) := φh.right_inv ht
    have := φh.injOn hin hq (hfw.trans hfq.symm)
    exact congrArg Prod.snd this

/-! ## The first-order solution is the log-linear Markov NK model -/

/-- The derivative of `Q` in the disturbances at the steady state. -/
noncomputable def DQe (p : Par) (e : Fin 5 → ℝ) : Fin 4 → ℝ :=
  ![e 0 - p.σ * e 1, -((1 - p.α * p.β) * (p.σ * e 1 + e 2)),
    -((1 - p.α * p.β) * (-(p.ω * e 3) + e 4)), 0]

/-- The derivative of `N` in the disturbances at the steady state. -/
noncomputable def DNe (p : Par) (e : Fin 5 → ℝ) : Fin 4 → ℝ := ![p.σ * e 1, 0, 0, 0]

/-- Woodford (2003), App. A.3: the derivative of `Q` along `t ↦ (te, 0)` is `DQ_e e`. -/
theorem hasDerivAt_Qmap_eps (e : Fin 5 → ℝ) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => Qmap p (t • e, 0) i) (DQe p e i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := hasDerivAt_exp_line (-(e 0 - p.σ * e 1)) (-1)
    refine (h.congr_deriv (by simp [DQe])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring_nf
  · have h := (hasDerivAt_exp_line 0 1).sub
      (hasDerivAt_exp_line (p.σ * e 1 + e 2) (1 - p.α * p.β))
    refine (h.congr_deriv (by simp [DQe])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · have h := (hasDerivAt_exp_line 0 1).sub
      (hasDerivAt_exp_line (-(p.ω * e 3) + e 4) (1 - p.α * p.β))
    refine (h.congr_deriv (by simp [DQe])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.sub_apply]
    ring_nf
  · simp only [Qmap, DQe, Matrix.cons_val, Pi.zero_apply]
    simp only [mul_zero, sub_self, neg_zero, zero_div, Real.exp_zero, mul_zero, add_zero]
    exact hasDerivAt_const _ _

/-- Woodford (2003), App. A.3: the derivative of `N` along `t ↦ (te, 0)` is `DN_e e`. -/
theorem hasDerivAt_Nmap_eps (e : Fin 5 → ℝ) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => Nmap p (t • e, 0) i) (DNe p e i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := hasDerivAt_exp_line (p.σ * e 1) 1
    refine (h.congr_deriv (by simp [DNe])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring_nf
  · simp only [Nmap, DNe, Matrix.cons_val, Pi.zero_apply, mul_zero, add_zero, Real.exp_zero,
      mul_one]
    exact hasDerivAt_const _ _
  · simp only [Nmap, DNe, Matrix.cons_val, Pi.zero_apply, mul_zero, add_zero, Real.exp_zero,
      mul_one]
    exact hasDerivAt_const _ _
  · simp only [Nmap, DNe, Matrix.cons_val]
    exact hasDerivAt_const _ _

/-- Woodford (2003), App. A.3: the derivative of the residual in the amplitude at the steady
state, `(∂Φ/∂ε)(x) = DQ_e ξ(x) + M[DN_e ξ](x)`. -/
noncomputable def Deps (p : Par) (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) : S → Fin 4 → ℝ :=
  fun s => DQe p (ξ s) + Mv (chainOp P) (fun s' => DNe p (ξ s')) s

/-- Woodford (2003), App. A.3: the derivative of the residual in the amplitude is `∂Φ/∂ε`. -/
theorem hasDerivAt_PhiS_eps (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) :
    HasDerivAt (fun t : ℝ => PhiS p P ξ (t, 0)) (Deps p P ξ) 0 := by
  rw [hasDerivAt_pi]
  intro s
  rw [hasDerivAt_pi]
  intro i
  have hQ := hasDerivAt_Qmap_eps (p := p) (ξ s) i
  have hN : ∀ s' ∈ (Finset.univ : Finset S), HasDerivAt
      (fun t : ℝ => P s s' * Nmap p (t • ξ s', 0) i) (P s s' * DNe p (ξ s') i) 0 :=
    fun s' _ => (hasDerivAt_Nmap_eps (ξ s') i).const_mul (P s s')
  have h := hQ.add (HasDerivAt.sum hN)
  convert h using 1
  · funext t
    simp only [PhiS_apply, Pi.zero_apply, Pi.add_apply, Finset.sum_apply]
  · simp only [Deps, Mv, chainOp, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]

/-- Woodford (2003), App. A.3 (**the first-order solution is the solution of the
linearised Markov model**): if `ε ↦ z_ε` is a family of Markov equilibria near `ε = 0` with
`z₀ = 0` and derivative `z₁` at `0`, then `L z₁ + ∂Φ/∂ε = 0`. -/
theorem firstOrder (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) {z : ℝ → S → Fin 4 → ℝ}
    {z1 : S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hz : HasDerivAt z z1 0)
    (heq : ∀ᶠ ε in 𝓝 0, IsMarkovEqm p (chainOp P) ξ ε (z ε)) :
    Lop p (chainOp P) z1 + Deps p P ξ = 0 := by
  have hd : HasFDerivAt (PhiS p P ξ) (fderiv ℝ (PhiS p P ξ) (0, 0)) (0, 0) :=
    ((contDiff_PhiS (n := 1) P ξ).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun ε : ℝ => (ε, z ε)) ((1 : ℝ), z1) 0 := (hasDerivAt_id 0).prodMk hz
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp [hz0])
  have h0 : HasDerivAt (fun ε => PhiS p P ξ (ε, z ε)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : S → Fin 4 → ℝ)).congr_of_eventuallyEq
      (heq.mono fun ε hε => hε)
  have hu := hc.unique h0
  have hsplit : ((1 : ℝ), z1) = ((1 : ℝ), (0 : S → Fin 4 → ℝ)) + ((0 : ℝ), z1) := by simp
  rw [hsplit, map_add, fderiv_PhiS_apply] at hu
  have he : fderiv ℝ (PhiS p P ξ) (0, 0) (1, 0) = Deps p P ξ := by
    have hl1 : HasDerivAt (fun t : ℝ => (t, (0 : S → Fin 4 → ℝ))) ((1 : ℝ), 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const _ _)
    have hc1 := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl1 rfl
    exact hc1.unique (hasDerivAt_PhiS_eps P ξ)
  rw [he] at hu
  rw [add_comm]; exact hu

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) and Ch. 3, (2.19) (**the first-order solution in
equations**): `(ŷ₁, π₁, F̂₁, K̂₁) = z′(0)` satisfies, state by state, with `P` the transition
operator
* IS curve with the rule: `(σ + φ_y)ŷ₁ + φ_π π₁ − σPŷ₁ − Pπ₁ + ν − σĉ + σPĉ = 0`;
* `F̂₁ = (1−αβ)((1−σ)ŷ₁ + σĉ + τ̂) + αβP((θ−1)π₁ + F̂₁)`;
* `K̂₁ = (1−αβ)((1+ω)ŷ₁ − ωq + μ̂ʷ) + αβP(θ(1+ω)π₁ + K̂₁)`;
* `α(θ−1)π₁ = (1−α)(θ−1)(K̂₁ − F̂₁)/(1+ωθ)`. -/
theorem firstOrder_eqs (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ) {z : ℝ → S → Fin 4 → ℝ}
    {z1 : S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hz : HasDerivAt z z1 0)
    (heq : ∀ᶠ ε in 𝓝 0, IsMarkovEqm p (chainOp P) ξ ε (z ε)) (s : S) :
    (p.σ + p.φy) * z1 s 0 + p.φ * z1 s 1 - p.σ * chainOp P (fun s' => z1 s' 0) s -
        chainOp P (fun s' => z1 s' 1) s + ξ s 0 - p.σ * ξ s 1 +
        p.σ * chainOp P (fun s' => ξ s' 1) s = 0 ∧
    z1 s 2 = (1 - p.α * p.β) * ((1 - p.σ) * z1 s 0 + p.σ * ξ s 1 + ξ s 2) +
        p.α * p.β * ((p.θ - 1) * chainOp P (fun s' => z1 s' 1) s +
          chainOp P (fun s' => z1 s' 2) s) ∧
    z1 s 3 = (1 - p.α * p.β) * ((1 + p.ω) * z1 s 0 - p.ω * ξ s 3 + ξ s 4) +
        p.α * p.β * (p.θ * (1 + p.ω) * chainOp P (fun s' => z1 s' 1) s +
          chainOp P (fun s' => z1 s' 3) s) ∧
    p.α * (p.θ - 1) * z1 s 1 = (1 - p.α) * (p.θ - 1) * (z1 s 3 - z1 s 2) / p.c0 := by
  have h := firstOrder P ξ hz0 hz heq
  have hc := Lop_apply (p := p) (chainOp P) z1 s
  have hσ : Mv (chainOp P) (fun s' => DNe p (ξ s')) s 0 =
      p.σ * chainOp P (fun s' => ξ s' 1) s := by
    simp only [Mv, DNe, Matrix.cons_val_zero, chainOp, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hz : ∀ i : Fin 4, i ≠ 0 → Mv (chainOp P) (fun s' => DNe p (ξ s')) s i = 0 := by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    all_goals simp [Mv, DNe, chainOp]
  have e : ∀ i, Lop p (chainOp P) z1 s i + (DQe p (ξ s) i +
      Mv (chainOp P) (fun s' => DNe p (ξ s')) s i) = 0 := fun i => by
    have := congrFun (congrFun h s) i
    simpa [Deps] using this
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  rw [hσ] at e0
  rw [hz 1 (by decide)] at e1
  rw [hz 2 (by decide)] at e2
  rw [hz 3 (by decide)] at e3
  rw [hc.1] at e0
  rw [hc.2.1] at e1
  rw [hc.2.2.1] at e2
  rw [hc.2.2.2] at e3
  simp only [DQe, Matrix.cons_val] at e0 e1 e2 e3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Woodford (2003), Ch. 3, (2.19)–(2.20) and §5, (5.4) at first order (**the NKPC of the
first-order solution**): `π₁ = κ(ŷ₁ − ŷⁿ₁) + βPπ₁` with the natural rate
`ŷⁿ = (ωq + σĉ − μ̂ʷ + τ̂)/(ω + σ)` (`LargeDistortions`' `YnA` at `s_C = 1`, `Ĝ = 0`). -/
theorem firstOrder_nkpc (hp : p.Std) (P : S → S → ℝ) (ξ : S → Fin 5 → ℝ)
    {z : ℝ → S → Fin 4 → ℝ} {z1 : S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hz : HasDerivAt z z1 0)
    (heq : ∀ᶠ ε in 𝓝 0, IsMarkovEqm p (chainOp P) ξ ε (z ε)) (s : S) :
    z1 s 1 = p.κ * (z1 s 0 - (p.ω * ξ s 3 + p.σ * ξ s 1 - ξ s 4 + ξ s 2) / (p.ω + p.σ)) +
      p.β * chainOp P (fun s' => z1 s' 1) s := by
  obtain ⟨-, h2, h3, h4⟩ := firstOrder_eqs P ξ hz0 hz heq s
  have hG : ∀ s', z1 s' 3 - z1 s' 2 = p.cR * z1 s' 1 := fun s' => by
    obtain ⟨-, -, -, h4'⟩ := firstOrder_eqs P ξ hz0 hz heq s'
    have hc0 := hp.c0_pos.ne'
    have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
    have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
    unfold Par.cR
    field_simp at h4' ⊢
    linear_combination -h4'
  have hMG : chainOp P (fun s' => z1 s' 3) s - chainOp P (fun s' => z1 s' 2) s =
      p.cR * chainOp P (fun s' => z1 s' 1) s := by
    have e1 := M_lin (chainOp P) 1 (-1) (fun s' => z1 s' 3) (fun s' => z1 s' 2) s
    have e2 : (fun s' => 1 * z1 s' 3 + -1 * z1 s' 2) =
        fun s' => p.cR * z1 s' 1 + 0 * z1 s' 1 := by
      funext s'; rw [← hG s']; ring
    rw [e2, M_lin] at e1
    linarith
  have hk' : p.κ * p.cR = (1 - p.α * p.β) * (p.ω + p.σ) := by
    rw [hp.κ_eq]; field_simp [hp.cR_pos.ne']
  have hab := hp.ab_c
  have hωσ : p.ω + p.σ ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hcR := hp.cR_pos
  unfold Par.c0 at hab
  have hGs := hG s
  have key : p.cR * (z1 s 1 - p.κ * z1 s 0 - p.β * chainOp P (fun s' => z1 s' 1) s) =
      -((1 - p.α * p.β) * (p.ω * ξ s 3 + p.σ * ξ s 1 - ξ s 4 + ξ s 2)) := by
    linear_combination h3 - h2 - hGs - z1 s 0 * hk' + p.α * p.β * hMG +
      chainOp P (fun s' => z1 s' 1) s * hab
  have h5 : z1 s 1 - p.κ * z1 s 0 - p.β * chainOp P (fun s' => z1 s' 1) s =
      -((1 - p.α * p.β) * (p.ω * ξ s 3 + p.σ * ξ s 1 - ξ s 4 + ξ s 2)) / p.cR := by
    rw [eq_div_iff hcR.ne']; linear_combination key
  have h6 : p.κ * ((p.ω * ξ s 3 + p.σ * ξ s 1 - ξ s 4 + ξ s 2) / (p.ω + p.σ)) =
      (1 - p.α * p.β) * (p.ω * ξ s 3 + p.σ * ξ s 1 - ξ s 4 + ξ s 2) / p.cR := by
    rw [hp.κ_eq]; field_simp
  rw [neg_div, ← h6] at h5
  linear_combination h5

end Woodford.StabilizationWelfare.NonlinearNKMarkov
