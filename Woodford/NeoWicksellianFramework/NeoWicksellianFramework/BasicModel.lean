/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.ForwardSolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The basic neo-Wicksellian model

Woodford (2003), *Interest and Prices*, Chapter 4, §1 (pp. 238–247).

Woodford (2003), *Interest and Prices*, Chapter 4, §1 (pp. 238–247).

All model equations are stated for an arbitrary `ExpectationSystem`, so every result holds under
perfect foresight and under genuine uncertainty.

## The nonlinear model

* `Euler11`, `Bound12`, `Transv13`, `Index14`, `FOC15`, `Taylor16`: equations (1.1)–(1.6), with
  (1.2) a genuine summability condition, (1.3) a genuine limit and (1.5) a genuine infinite sum;
  `IsREE`: the **Definition** of rational-expectations equilibrium (pp. 241–242).
* (1.4): `HomogeneousOne`; the Dixit–Stiglitz `cesAgg` of fn. 6 is homogeneous of degree one
  (`cesAgg_homogeneous`), satisfies `𝒫(P, P) = P` (`cesAgg_diag`) and is injective in the reset
  price (`cesAgg_injective`); homogeneity makes gross inflation `𝒫(p*_t/P_{t−1}, 1)`
  (`gross_inflation_eq`) and zero inflation equivalent to `p*_t = P_{t−1}` (`zero_inflation_iff`);
  `index_partials_sum` (Euler's theorem `a + b = 1`) and `hasFDerivAt_log_index` (the log-linear
  index law for any homogeneous `𝒫`).

## Log-linearisation as exact derivatives

* `quadratic_remainder`: a `C²` function has a quadratic first-order remainder;
  `hasDerivAt_neg_log_E_exp`: hence, along bounded random directions, the map
  `ε ↦ −log E_t[exp(λ(ε a) − λ(ε b) − ε p)]` has derivative `E_t[Db − Da + p]` (general state
  space).
* (1.7): `euler_log_form` writes (1.1) in logs; `euler_deriv` — the exact derivative of the log
  of (1.1) at the steady state is `σ⁻¹E_t[(Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t)] + E_tπ_{t+1}` with
  `σ = s_C σ̃` (`sigmaIS`, fn. 10) and `g = Ĝ + s_C c̄` (`gcoef`, fn. 11), for `C²` utility;
  `is17_iff`: equating `î_t` to it is (1.7) (`IS17`).
* (1.10): the Chapter 3 derivation is restated (`hasFDerivAt_logIndexFn`, `hasDerivAt_focPath`,
  `eq26_iff_deriv_zero`, `prop35`); `eq110_iff` is (1.10) in this chapter's notation.
* (1.11): `hasFDerivAt_taylorLog` — the derivative of the Taylor rule (1.6) in logs is
  `ī_t + φ_π(π_t − π̄) + φ_y Ŷ_t/4` with `φ_π = βφ₁`, `φ_y = 4βȲφ_Y`, `ī = βφ_ν ν − φ_π(π* − π̄)`.

## The forward IS relation (1.8)–(1.9) and footnote 12

* `is17_iterate`, `eq18_iff_eq19`: for a solution of (1.7), the limit hypothesis (1.9) holds iff
  the series of (1.8) converges (as the limit of its partial sums) with
  `Ŷ_t = Ŷ_∞ + g_t − σ ∑_j E_t(î_{t+j} − π_{t+j+1})`; `eq18_tsum` (summable case);
  `eq19_needed`: a bounded solution for which (1.9), hence (1.8), fails — the hypothesis is
  needed.
* Footnote 12: `fn12_nkpc` (`Ŷ_∞ = (1 − β)π_∞/κ` under the NKPC), `fn12_newClassical` (`Ŷ_∞ = 0`
  under the New Classical AS relation, with no condition on inflation), `fn12_indexation`
  (`x_∞ = 0` under (2.36) with `γ = 1` whenever inflation is bounded), `yinf_eq_lim`.

## The gap form (1.12)–(1.15)

`rnHat` (1.15), `IS112` (1.12), `is17_iff_is112`, `eq110_iff_eq113`, `eq111_iff_eq114` (the two
rule representations and their intercepts), `xbar` (`x̄ = (1 − β)π̄/κ`), `const_nkpc_iff`,
`rule114_at_target`.

Survey error E17 (p. 247, "an interest-rate rule such as (1.15)"): confirmed — (1.15) is the
definition of `r̂ⁿ`; the rule is (1.14).
-/

namespace Woodford.NeoWicksellianFramework.BasicModel

open Filter Topology

variable {Ω X : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The nonlinear equilibrium conditions (1.1)–(1.6)

Price indexing (as in the Chapter 3 project): `P (t + 1)` is the price index `P_t` of period `t`
and `P 0 = P_{−1}`, so `P (t + 1)` is known at `t` and `P (t + 1) / P t` is gross inflation
`Π_t`. Consumption is `C_t = Y_t − G_t`; the marginal utility of real income is
`u_c(C_t; ξ_t)`. -/

/-- Woodford (2003), eq. (1.1), p. 239 (**the Euler equation**) at date `t`:
`1 + i_t = β⁻¹ {E_t[u_c(Y_{t+1} − G_{t+1}; ξ_{t+1}) P_t / (u_c(Y_t − G_t; ξ_t) P_{t+1})]}⁻¹`. -/
def Euler11 (β : ℝ) (uc : ℝ → X → ℝ) (G : ℕ → Ω → ℝ) (ξ : ℕ → Ω → X) (P Y i : ℕ → Ω → ℝ)
    (t : ℕ) : Prop :=
  ∀ ω, 1 + i t ω = β⁻¹ * (𝔼.E t (fun ω' => uc (Y (t + 1) ω' - G (t + 1) ω') (ξ (t + 1) ω') *
    P (t + 1) ω' / (uc (Y t ω' - G t ω') (ξ t ω') * P (t + 2) ω')) ω)⁻¹

/-- Woodford (2003), eq. (1.2), p. 239 (**the household's spending bound**): for every date `t`
the series `∑_{T ≥ t} β^T E_t[u_c(Y_T − G_T; ξ_T)(Y_T − G_T)]` converges. -/
def Bound12 (β : ℝ) (uc : ℝ → X → ℝ) (G : ℕ → Ω → ℝ) (ξ : ℕ → Ω → X) (Y : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t ω, Summable (fun k => β ^ (t + k) * 𝔼.E t (fun ω' =>
    uc (Y (t + k) ω' - G (t + k) ω') (ξ (t + k) ω') * (Y (t + k) ω' - G (t + k) ω')) ω)

/-- Woodford (2003), eq. (1.3), p. 240 (**the transversality condition**):
`lim_{T→∞} β^T E_t[u_c(Y_T − G_T; ξ_T) D_T / P_T] = 0` for every date `t`. -/
def Transv13 (β : ℝ) (uc : ℝ → X → ℝ) (G : ℕ → Ω → ℝ) (ξ : ℕ → Ω → X) (D P Y : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (fun ω' =>
    uc (Y T ω' - G T ω') (ξ T ω') * D T ω' / P (T + 1) ω') ω) atTop (𝓝 0)

/-- Woodford (2003), eq. (1.4), p. 240 (**the law of motion of the price index**):
`P_t = 𝒫(p*_t, P_{t−1})`. -/
def Index14 (Pagg : ℝ → ℝ → ℝ) (P pstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, P (t + 1) ω = Pagg (pstar t ω) (P t ω)

/-- Woodford (2003), eq. (1.5), pp. 240–241 (**the optimal-pricing condition**): for every date
`t` the series `∑_{T ≥ t} (αβ)^{T−t} E_t[u_c(Y_T − G_T; ξ_T) P_T⁻¹ Π₁(p*_t, p*_t, P_T; Y_T, ξ_T)]`
converges and equals zero. -/
def FOC15 (α β : ℝ) (uc : ℝ → X → ℝ) (Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ) (G : ℕ → Ω → ℝ)
    (ξ : ℕ → Ω → X) (P Y pstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable (fun k => (α * β) ^ k * 𝔼.E t (fun ω' =>
      uc (Y (t + k) ω' - G (t + k) ω') (ξ (t + k) ω') / P (t + k + 1) ω' *
        Pi1 (pstar t ω') (pstar t ω') (P (t + k + 1) ω') (Y (t + k) ω') (ξ (t + k) ω')) ω) ∧
    ∑' k, (α * β) ^ k * 𝔼.E t (fun ω' =>
      uc (Y (t + k) ω' - G (t + k) ω') (ξ (t + k) ω') / P (t + k + 1) ω' *
        Pi1 (pstar t ω') (pstar t ω') (P (t + k + 1) ω') (Y (t + k) ω') (ξ (t + k) ω')) ω = 0

/-- Woodford (2003), eq. (1.6), p. 241 (**the Taylor rule**): `i_t = φ(Π_t/Π*_t; Y_t, ν_t)`. -/
def Taylor16 (φ : ℝ → ℝ → ℝ → ℝ) (PiStar ν P Y i : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i t ω = φ (P (t + 1) ω / P t ω / PiStar t ω) (Y t ω) (ν t ω)

/-- Woodford (2003), **Definition** (rational-expectations equilibrium of the basic
neo-Wicksellian model), pp. 241–242: processes `(P, Y, i)` (with the reset price `p*` of
(1.4)–(1.5)) satisfying (1.1)–(1.6) at all dates `t ≥ 0`, given the exogenous disturbances
`(G, ξ, Π*, ν)` and the path `D` of government liabilities. -/
def IsREE (α β : ℝ) (uc : ℝ → X → ℝ) (Pagg : ℝ → ℝ → ℝ) (Pi1 : ℝ → ℝ → ℝ → ℝ → X → ℝ)
    (φ : ℝ → ℝ → ℝ → ℝ) (G : ℕ → Ω → ℝ) (ξ : ℕ → Ω → X) (D PiStar ν P Y i pstar : ℕ → Ω → ℝ) :
    Prop :=
  (∀ t, Euler11 𝔼 β uc G ξ P Y i t) ∧ Bound12 𝔼 β uc G ξ Y ∧ Transv13 𝔼 β uc G ξ D P Y ∧
    Index14 Pagg P pstar ∧ FOC15 𝔼 α β uc Pi1 G ξ P Y pstar ∧ Taylor16 φ PiStar ν P Y i

/-! ### (1.4): homogeneity of the price-index law of motion -/

/-- Woodford (2003), p. 240: `𝒫(p, P)` is homogeneous of degree one (on positive prices). -/
def HomogeneousOne (Pagg : ℝ → ℝ → ℝ) : Prop :=
  ∀ c p P : ℝ, 0 < c → 0 < p → 0 < P → Pagg (c * p) (c * P) = c * Pagg p P

/-- Woodford (2003), fn. 6, p. 240: the Dixit–Stiglitz law of motion
`𝒫(p, P) = [(1 − α) p^{1−θ} + α P^{1−θ}]^{1/(1−θ)}`. -/
noncomputable def cesAgg (α θ p P : ℝ) : ℝ :=
  ((1 - α) * p ^ (1 - θ) + α * P ^ (1 - θ)) ^ (1 - θ)⁻¹

/-- Woodford (2003), fn. 6, p. 240: the Dixit–Stiglitz `𝒫` is homogeneous of degree one, for
`0 ≤ α ≤ 1`, `θ ≠ 1`. -/
theorem cesAgg_homogeneous {α θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hθ : θ ≠ 1) :
    HomogeneousOne (cesAgg α θ) := by
  intro c p P hc hp hP
  have hs : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have hS : 0 ≤ (1 - α) * p ^ (1 - θ) + α * P ^ (1 - θ) := by
    have h1 : 0 ≤ 1 - α := by linarith
    positivity
  unfold cesAgg
  rw [Real.mul_rpow hc.le hp.le, Real.mul_rpow hc.le hP.le,
    show (1 - α) * (c ^ (1 - θ) * p ^ (1 - θ)) + α * (c ^ (1 - θ) * P ^ (1 - θ))
      = c ^ (1 - θ) * ((1 - α) * p ^ (1 - θ) + α * P ^ (1 - θ)) by ring,
    Real.mul_rpow (Real.rpow_nonneg hc.le _) hS, Real.rpow_rpow_inv hc.le hs]

/-- Woodford (2003), p. 240: `𝒫(P, P) = P` for the Dixit–Stiglitz index (a reset price equal
to last period's index leaves the index unchanged). -/
theorem cesAgg_diag (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) {P : ℝ} (hP : 0 < P) : cesAgg α θ P P = P := by
  have hs : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  unfold cesAgg
  rw [show (1 - α) * P ^ (1 - θ) + α * P ^ (1 - θ) = P ^ (1 - θ) by ring,
    Real.rpow_rpow_inv hP.le hs]

/-- Woodford (2003), p. 240: the Dixit–Stiglitz `𝒫(·, P)` is injective in the reset price
(`α ≠ 1`, `θ ≠ 1`, positive prices). -/
theorem cesAgg_injective {α θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : θ ≠ 1) {p q P : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hP : 0 < P) (h : cesAgg α θ p P = cesAgg α θ q P) : p = q := by
  have hs : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h1 : 0 < 1 - α := by linarith
  have hSp : 0 ≤ (1 - α) * p ^ (1 - θ) + α * P ^ (1 - θ) := by positivity
  have hSq : 0 ≤ (1 - α) * q ^ (1 - θ) + α * P ^ (1 - θ) := by positivity
  have h2 : (1 - α) * p ^ (1 - θ) + α * P ^ (1 - θ) = (1 - α) * q ^ (1 - θ) + α * P ^ (1 - θ) := by
    have := congrArg (fun z => z ^ (1 - θ)) h
    simp only [cesAgg] at this
    rwa [← Real.rpow_mul hSp, ← Real.rpow_mul hSq, inv_mul_cancel₀ hs, Real.rpow_one,
      Real.rpow_one] at this
  have h3 : p ^ (1 - θ) = q ^ (1 - θ) := by
    have := mul_left_cancel₀ h1.ne' (add_right_cancel h2)
    exact this
  rw [← Real.rpow_rpow_inv hp.le hs, ← Real.rpow_rpow_inv hq.le hs, h3]

/-- Woodford (2003), eq. (1.4), p. 240 (**homogeneity gives gross inflation as a function of the
relative reset price**): if `𝒫` is homogeneous of degree one, then
`Π_t = P_t / P_{t−1} = 𝒫(p*_t / P_{t−1}, 1)`. -/
theorem gross_inflation_eq {Pagg : ℝ → ℝ → ℝ} (hP : HomogeneousOne Pagg) {pstar Pprev : ℝ}
    (hps : 0 < pstar) (hPp : 0 < Pprev) :
    Pagg pstar Pprev / Pprev = Pagg (pstar / Pprev) 1 := by
  have h := hP Pprev (pstar / Pprev) 1 hPp (div_pos hps hPp) one_pos
  rw [mul_div_cancel₀ _ hPp.ne', mul_one] at h
  rw [h]
  field_simp

/-- Woodford (2003), eq. (1.4), p. 240, and p. 247 (**zero inflation ⟺ the reset price equals last
period's index**): if `𝒫` is homogeneous of degree one, `𝒫(1, 1) = 1` and `𝒫(·, 1)` is injective
on positive prices, then `P_t = P_{t−1}` iff `p*_t = P_{t−1}`. -/
theorem zero_inflation_iff {Pagg : ℝ → ℝ → ℝ} (hP : HomogeneousOne Pagg) (h11 : Pagg 1 1 = 1)
    (hinj : ∀ p q, 0 < p → 0 < q → Pagg p 1 = Pagg q 1 → p = q) {pstar Pprev : ℝ}
    (hps : 0 < pstar) (hPp : 0 < Pprev) : Pagg pstar Pprev = Pprev ↔ pstar = Pprev := by
  have hg := gross_inflation_eq hP hps hPp
  constructor
  · intro h
    rw [h, div_self hPp.ne'] at hg
    have := hinj (pstar / Pprev) 1 (div_pos hps hPp) one_pos (by rw [← hg, h11])
    field_simp at this
    exact this
  · intro h
    rw [h] at hg ⊢
    rw [div_self hPp.ne', h11] at hg
    field_simp at hg
    exact hg

/-! ### Exact derivatives under `E_t`: the quadratic-remainder lemma -/

/-- Woodford (2003), §1.2, p. 243 (the log-linearisation step, made exact): a function that is
`C²` at `0` has a quadratic first-order remainder near `0`,
`|f(h) − f(0) − Df(0) h| ≤ C ‖h‖²`. (Proved here: `Df` is `C¹`, hence locally Lipschitz, and the
mean value inequality applies on the ball of radius `‖h‖`.) -/
theorem quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) :
    ∃ C r : ℝ, 0 < r ∧ ∀ h : E, ‖h‖ < r → |f h - f 0 - fderiv ℝ f 0 h| ≤ C * ‖h‖ ^ 2 := by
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hlip⟩ := h1.exists_lipschitzOnWith
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem ht hev)
  refine ⟨K, r, hr, fun h hh => ?_⟩
  have hsub : Metric.closedBall (0 : E) ‖h‖ ⊆ Metric.ball 0 r :=
    Metric.closedBall_subset_ball hh
  have hdiff : ∀ y ∈ Metric.closedBall (0 : E) ‖h‖, DifferentiableAt ℝ f y := by
    intro y hy
    have hy2 : ContDiffAt ℝ 2 f y := (hball (hsub hy)).2
    exact hy2.differentiableAt (by norm_num)
  have h0t : (0 : E) ∈ t := (hball (Metric.mem_ball_self hr)).1
  have hbound : ∀ y ∈ Metric.closedBall (0 : E) ‖h‖,
      ‖fderiv ℝ f y - fderiv ℝ f 0‖ ≤ K * ‖h‖ := by
    intro y hy
    have hyt : y ∈ t := (hball (hsub hy)).1
    have := lipschitzOnWith_iff_norm_sub_le.mp hlip hyt h0t
    rw [sub_zero] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
    simpa using hy
  have := Convex.norm_image_sub_le_of_norm_fderiv_le' (x := 0) (y := h) hdiff hbound
    (convex_closedBall 0 ‖h‖)
    (Metric.mem_closedBall_self (norm_nonneg h)) (by simp)
  rw [sub_zero, Real.norm_eq_abs] at this
  calc |f h - f 0 - fderiv ℝ f 0 h| ≤ K * ‖h‖ * ‖h‖ := this
    _ = K * ‖h‖ ^ 2 := by ring

/-- Woodford (2003), §1.2, p. 243 (differentiating under `E_t`; restated from the Chapter 3
project): if the second-order remainder of `z ↦ g z` at `x` is bounded by `C h²` uniformly in the
state, then `z ↦ E_t[g z]` has derivative `E_t[g']` at `x`. -/
theorem hasDerivAt_E_of_remainder {g : ℝ → Ω → ℝ} {g' : Ω → ℝ} {x C δ : ℝ} (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |g (x + h) ω - g x ω - h * g' ω| ≤ C * h ^ 2)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun z => 𝔼.E t (g z) ω) (𝔼.E t g' ω) x := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun h => 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω)
      =O[𝓝 0] fun h : ℝ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
    have key : 𝔼.E t (g (x + h)) ω - 𝔼.E t (g x) ω - h • 𝔼.E t g' ω
        = 𝔼.E t (g (x + h) - g x - h • g') ω := by
      simp [map_sub, map_smul]
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hrem h hh' ω') t ω
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Woodford (2003), §1.2, p. 243, and Chapter 2, eq. (1.32), p. 79 (**the derivative of the exact
log Euler map, general state space**): let `λ : E → ℝ` vanish at `0` and have a quadratic
first-order remainder with derivative `D` (e.g. `λ` is `C²`, `quadratic_remainder`), and let
`a, b, p` be bounded random directions. Then
`ε ↦ −log E_t[exp(λ(ε a) − λ(ε b) − ε p)]` has derivative `E_t[D b − D a + p]` at `ε = 0`. -/
theorem hasDerivAt_neg_log_E_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {lam : E → ℝ} {D : E →L[ℝ] ℝ} {C r K : ℝ} (hr : 0 < r) (hlam0 : lam 0 = 0)
    (hrem : ∀ h : E, ‖h‖ < r → |lam h - lam 0 - D h| ≤ C * ‖h‖ ^ 2)
    {a b : Ω → E} {p : Ω → ℝ} (ha : ∀ ω, ‖a ω‖ ≤ K) (hb : ∀ ω, ‖b ω‖ ≤ K)
    (hp : ∀ ω, |p ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' =>
        Real.exp (lam (ε • a ω') - lam (ε • b ω') - ε * p ω')) ω))
      (𝔼.E t (fun ω' => D (b ω') - D (a ω') + p ω') ω) 0 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hp ω)
  set B := ‖D‖ * K * 2 + K with hB
  set c := |C| * K ^ 2 with hc
  set A := B + 2 * c with hA
  have hc0 : 0 ≤ c := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hA0 : 0 ≤ A := by positivity
  set g' : Ω → ℝ := fun ω' => D (a ω') - D (b ω') - p ω' with hg'
  have hDv : ∀ v : E, ‖v‖ ≤ K → |D v| ≤ ‖D‖ * K := fun v hv => by
    rw [← Real.norm_eq_abs]
    exact (D.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg D))
  have hg'b : ∀ ω', |g' ω'| ≤ B := by
    intro ω'
    simp only [hg']
    calc |D (a ω') - D (b ω') - p ω'| ≤ |D (a ω')| + |D (b ω')| + |p ω'| := by
          have h1 := abs_sub (D (a ω') - D (b ω')) (p ω')
          have h2 := abs_sub (D (a ω')) (D (b ω'))
          linarith
      _ ≤ ‖D‖ * K + ‖D‖ * K + K :=
          add_le_add (add_le_add (hDv _ (ha ω')) (hDv _ (hb ω'))) (hp ω')
      _ = B := by rw [hB]; ring
  -- the remainder of `λ` along a bounded direction
  have hlr : ∀ (ε : ℝ) (v : E), ‖v‖ ≤ K → |ε| * (K + 1) < r →
      |lam (ε • v) - ε * D v| ≤ c * ε ^ 2 := by
    intro ε v hv hε
    have hn : ‖ε • v‖ ≤ |ε| * K := by
      rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hv (abs_nonneg ε)
    have hlt : ‖ε • v‖ < r := by nlinarith [abs_nonneg ε]
    have h := hrem (ε • v) hlt
    rw [hlam0, sub_zero, map_smul, smul_eq_mul] at h
    calc |lam (ε • v) - ε * D v| ≤ C * ‖ε • v‖ ^ 2 := h
      _ ≤ |C| * (|ε| * K) ^ 2 := by
          refine mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (norm_nonneg _) hn 2)
            (sq_nonneg _) (abs_nonneg C)
      _ = c * ε ^ 2 := by rw [hc, mul_pow, sq_abs]; ring
  set δ := min (r / (K + 1)) (min 1 (1 / (A + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (div_pos hr (by linarith)) (lt_min one_pos (by positivity))
  set g : ℝ → Ω → ℝ := fun ε ω' => Real.exp (lam (ε • a ω') - lam (ε • b ω') - ε * p ω')
    with hg
  have hrem' : ∀ h, |h| < δ → ∀ ω',
      |g (0 + h) ω' - g 0 ω' - h * g' ω'| ≤ (A ^ 2 + 2 * c) * h ^ 2 := by
    intro h hh ω'
    have hh1 : |h| < r / (K + 1) := lt_of_lt_of_le hh (min_le_left _ _)
    have hh2 : |h| < 1 := lt_of_lt_of_le hh ((min_le_right _ _).trans (min_le_left _ _))
    have hh3 : |h| < 1 / (A + 1) := lt_of_lt_of_le hh ((min_le_right _ _).trans (min_le_right _ _))
    have hr' : |h| * (K + 1) < r := by rwa [lt_div_iff₀ (by linarith)] at hh1
    have ra := hlr h (a ω') (ha ω') hr'
    have rb := hlr h (b ω') (hb ω') hr'
    set e := lam (h • a ω') - lam (h • b ω') - h * p ω' with he
    have hlin : |e - h * g' ω'| ≤ 2 * c * h ^ 2 := by
      have : e - h * g' ω' = (lam (h • a ω') - h * D (a ω')) - (lam (h • b ω') - h * D (b ω')) := by
        simp only [he, hg']; ring
      rw [this]
      have := abs_sub (lam (h • a ω') - h * D (a ω')) (lam (h • b ω') - h * D (b ω'))
      linarith
    have hhg : |h * g' ω'| ≤ |h| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hg'b ω') (abs_nonneg h)
    have hsq : h ^ 2 ≤ |h| := by
      rw [← sq_abs]; nlinarith [abs_nonneg h]
    have he1 : |e| ≤ |h| * A := by
      have := abs_sub_abs_le_abs_sub e (h * g' ω')
      rw [hA]; nlinarith [abs_nonneg h]
    have he2 : |e| ≤ 1 := by
      have : |h| * (A + 1) < 1 := by rwa [lt_div_iff₀ (by linarith)] at hh3
      nlinarith [abs_nonneg h]
    have hexp := Real.abs_exp_sub_one_sub_id_le he2
    have hg0 : g 0 ω' = 1 := by simp [hg, hlam0]
    rw [zero_add, hg0]
    have hgh : g h ω' = Real.exp e := rfl
    rw [hgh]
    have hesq : e ^ 2 ≤ A ^ 2 * h ^ 2 := by
      rw [← sq_abs e, ← sq_abs h, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg e) (by linarith [he1]) 2
    calc |Real.exp e - 1 - h * g' ω'| ≤ |Real.exp e - 1 - e| + |e - h * g' ω'| := by
          have : Real.exp e - 1 - h * g' ω' = (Real.exp e - 1 - e) + (e - h * g' ω') := by ring
          rw [this]; exact abs_add_le _ _
      _ ≤ A ^ 2 * h ^ 2 + 2 * c * h ^ 2 := add_le_add (hexp.trans hesq) hlin
      _ = (A ^ 2 + 2 * c) * h ^ 2 := by ring
  have hE := hasDerivAt_E_of_remainder 𝔼 hδ0 hrem' t ω
  have h1 : 𝔼.E t (g 0) ω = 1 := by
    have : g 0 = fun _ => (1 : ℝ) := by funext ω'; simp [hg, hlam0]
    rw [this, 𝔼.const]
  have hlog := hE.log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at hlog
  convert hlog.neg using 1
  have hfun : (fun ω' => D (b ω') - D (a ω') + p ω') = -g' := by
    funext ω'; simp only [hg', Pi.neg_apply]; ring
  rw [hfun, map_neg]
  rfl

/-! ### (1.7) as the exact derivative of the log of (1.1) -/

/-- Woodford (2003), §1.2, p. 243 (and Chapter 2, eq. (1.33)): the log deviation of the marginal
utility of real income, `λ(Ŷ, Ĝ, ξ) = log u_c(Ȳ e^Ŷ − Ḡ − Ȳ Ĝ; ξ) − log u_c(C̄; 0)`, with
`C̄ = Ȳ − Ḡ` and `Ĝ = (G − Ḡ)/Ȳ` (restated from the Chapter 2 project). -/
noncomputable def lambdaG (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  Real.log (uc (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)) -
    Real.log (uc (Ybar - Gbar, 0))

/-- Woodford (2003), fn. 10, p. 243: `σ = s_C σ̃`, with `s_C = C̄/Ȳ` and
`σ̃ = −u_c/(C̄ u_cc)` the intertemporal elasticity of household expenditure. -/
noncomputable def sigmaIS (uc : ℝ × ℝ → ℝ) (Ybar Gbar ucc : ℝ) : ℝ :=
  ((Ybar - Gbar) / Ybar) * (-uc (Ybar - Gbar, 0) / (ucc * (Ybar - Gbar)))

/-- Woodford (2003), fn. 11, p. 243, and (2.3), p. 249: the coefficient of the preference shock
`ξ` in `g = Ĝ + s_C c̄`, `c̄ = −u_cξ ξ/(C̄ u_cc)`. -/
noncomputable def gcoef (Ybar Gbar ucc ucxi : ℝ) : ℝ :=
  (Ybar - Gbar) / Ybar * (-ucxi / ((Ybar - Gbar) * ucc))

/-- Woodford (2003), §1.2, p. 243 (restated from the Chapter 2 project, `hasFDerivAt_lambdaG`):
the derivative of `λ(Ŷ, Ĝ, ξ)` at the steady state is `−σ⁻¹(Ŷ − g)`, `σ = s_C σ̃`,
`g = Ĝ + s_C c̄`. -/
theorem hasFDerivAt_lambdaG {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc ucxi : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0)) :
    HasFDerivAt (lambdaG uc Ybar Gbar)
      ((-(sigmaIS uc Ybar Gbar ucc)⁻¹) •
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gcoef Ybar Gbar ucc ucxi •
            (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))) 0 := by
  set h : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)
    with hh
  have hd1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1)
      (Ybar • Real.exp (0 : ℝ × ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        Ybar • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) 0 := by
    have h1 := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ))).exp.const_mul Ybar).sub_const
      Gbar
    have h2 := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))).const_mul Ybar
    exact h1.sub h2
  have hd2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) 0 :=
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ)))
  have hd := hd1.prodMk hd2
  have h0 : h 0 = (Ybar - Gbar, 0) := by simp [hh]
  have huc' : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (h 0) := by rw [h0]; exact huc
  have hcomp := (huc'.comp (0 : ℝ × ℝ × ℝ) hd).log
    (by rw [Function.comp_apply, h0]; exact hu.ne')
  have hfin := hcomp.sub_const (Real.log (uc (Ybar - Gbar, 0)))
  refine hfin.congr_fderiv ?_
  have hC' : Ybar - Gbar ≠ 0 := hC.ne'
  ext
  · simp [h0, sigmaIS, gcoef]
    field_simp
  · simp [h0, sigmaIS, gcoef]
    field_simp
  · simp [h0, sigmaIS, gcoef]
    field_simp

/-- Woodford (2003), §1.2, p. 243: `λ` is `C²` at the steady state when `u_c` is `C²` there and
`u_c(C̄; 0) > 0`. -/
theorem contDiffAt_lambdaG {uc : ℝ × ℝ → ℝ} {Ybar Gbar : ℝ} (hu : 0 < uc (Ybar - Gbar, 0))
    (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0)) : ContDiffAt ℝ 2 (lambdaG uc Ybar Gbar) 0 := by
  set h : ℝ × ℝ × ℝ → ℝ × ℝ := fun p => (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)
    with hh
  have hin : ContDiff ℝ 2 h := by
    refine ContDiff.prodMk ?_ ?_
    · exact ((contDiff_const.mul (Real.contDiff_exp.comp contDiff_fst)).sub contDiff_const).sub
        (contDiff_const.mul (contDiff_fst.comp contDiff_snd))
    · exact contDiff_snd.comp contDiff_snd
  have h0 : h 0 = (Ybar - Gbar, 0) := by simp [hh]
  have hc : ContDiffAt ℝ 2 (uc ∘ h) 0 :=
    ContDiffAt.comp (0 : ℝ × ℝ × ℝ) (by rw [h0]; exact huc2) hin.contDiffAt
  exact (hc.log (by rw [Function.comp_apply, h0]; exact hu.ne')).sub contDiffAt_const

/-- Woodford (2003), §1.2, p. 243: `λ(0) = 0`. -/
theorem lambdaG_zero (uc : ℝ × ℝ → ℝ) (Ybar Gbar : ℝ) : lambdaG uc Ybar Gbar 0 = 0 := by
  simp [lambdaG]

/-- Woodford (2003), eq. (1.1), p. 239 (**(1.1) in logs**): with positive marginal utilities
`m_s = u_c(Y_s − G_s; ξ_s)` and prices, (1.1) holds at `t` iff
`log(β(1 + i_t)) = −log E_t[exp(log(m_{t+1}/m̄) − log(m_t/m̄) − log(P_{t+1}/P_t))]` for any
`m̄ > 0` (restated from the Chapter 2 project, `fisher_log_form`). -/
theorem euler_log_form {β mbar : ℝ} (hβ : 0 < β) (hm : 0 < mbar) {i m P : ℕ → Ω → ℝ}
    (t : ℕ) (hm0 : ∀ s ω, 0 < m s ω) (hP : ∀ s ω, 0 < P s ω) (hi : ∀ ω, 0 < 1 + i t ω)
    (hE : ∀ ω, 0 < 𝔼.E t (fun ω' => m (t + 1) ω' * P (t + 1) ω' / (m t ω' * P (t + 2) ω')) ω) :
    (∀ ω, 1 + i t ω = β⁻¹ *
        (𝔼.E t (fun ω' => m (t + 1) ω' * P (t + 1) ω' / (m t ω' * P (t + 2) ω')) ω)⁻¹) ↔
      ∀ ω, Real.log (β * (1 + i t ω)) =
        -Real.log (𝔼.E t (fun ω' => Real.exp (Real.log (m (t + 1) ω' / mbar) -
          Real.log (m t ω' / mbar) - Real.log (P (t + 2) ω' / P (t + 1) ω'))) ω) := by
  have hX : (fun ω' => Real.exp (Real.log (m (t + 1) ω' / mbar) -
      Real.log (m t ω' / mbar) - Real.log (P (t + 2) ω' / P (t + 1) ω'))) =
      fun ω' => m (t + 1) ω' * P (t + 1) ω' / (m t ω' * P (t + 2) ω') := by
    funext ω'
    have h1 := hm0 (t + 1) ω'
    have h2 := hm0 t ω'
    have h3 := hP (t + 1) ω'
    have h4 := hP (t + 2) ω'
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by positivity), Real.exp_log (by positivity),
      Real.exp_log (by positivity)]
    field_simp
  rw [hX]
  refine forall_congr' fun ω => ?_
  have hE' := hE ω
  have hi' := hi ω
  rw [← Real.log_inv]
  constructor
  · intro h
    rw [h]
    congr 1
    field_simp
  · intro h
    have h' := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (inv_pos.mpr hE')) h
    have hβ' : β ≠ 0 := hβ.ne'
    field_simp at h' ⊢
    linarith

/-- Woodford (2003), §1.2, p. 243: `λ(Ŷ, Ĝ, ξ) = log(u_c(Ȳe^Ŷ − Ḡ − ȲĜ; ξ)/u_c(C̄; 0))` when the
marginal utilities are positive, so `fun ω => λ(v_s ω)` is the `log(m_s/m̄)` of
`euler_log_form`. -/
theorem lambdaG_eq_log_div {uc : ℝ × ℝ → ℝ} {Ybar Gbar : ℝ} (hu : 0 < uc (Ybar - Gbar, 0))
    (p : ℝ × ℝ × ℝ) (hp : 0 < uc (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2)) :
    lambdaG uc Ybar Gbar p =
      Real.log (uc (Ybar * Real.exp p.1 - Gbar - Ybar * p.2.1, p.2.2) / uc (Ybar - Gbar, 0)) := by
  rw [lambdaG, Real.log_div hp.ne' hu.ne']

/-- Woodford (2003), eq. (1.7), p. 243 (**(1.7) is the exact derivative of the log of the Euler
equation (1.1)**, general state space): scale the deviations `v_s = (Ŷ_s, Ĝ_s, ξ_s)` and
inflation `π` by `ε`; if `u_c` is `C²` at the steady state `(C̄, 0)` with partial derivatives
`u_cc ≠ 0`, `u_cξ`, `u_c(C̄; 0) > 0`, and the directions are bounded, the exact log Euler map
`ε ↦ log(β(1 + i_t)) = −log E_t[exp(λ(ε v_{t+1}) − λ(ε v_t) − ε π_{t+1})]` (`euler_log_form`,
`lambdaG_eq_log_div`) has derivative `σ⁻¹ E_t[(Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t)] + E_t π_{t+1}` at
`ε = 0`, with `σ = s_C σ̃` (fn. 10) and `g = Ĝ + s_C c̄` (fn. 11). -/
theorem euler_deriv {uc : ℝ × ℝ → ℝ} {Ybar Gbar ucc ucxi K : ℝ} (hY : 0 < Ybar)
    (hC : 0 < Ybar - Gbar) (hu : 0 < uc (Ybar - Gbar, 0)) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucxi • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Gbar, 0))
    (huc2 : ContDiffAt ℝ 2 uc (Ybar - Gbar, 0)) {Yh Gh xi π : ℕ → Ω → ℝ}
    (hYb : ∀ s ω, |Yh s ω| ≤ K) (hGb : ∀ s ω, |Gh s ω| ≤ K) (hxb : ∀ s ω, |xi s ω| ≤ K)
    (hπb : ∀ s ω, |π s ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => -Real.log (𝔼.E t (fun ω' => Real.exp
        (lambdaG uc Ybar Gbar (ε • (Yh (t + 1) ω', Gh (t + 1) ω', xi (t + 1) ω')) -
          lambdaG uc Ybar Gbar (ε • (Yh t ω', Gh t ω', xi t ω')) - ε * π (t + 1) ω')) ω))
      ((sigmaIS uc Ybar Gbar ucc)⁻¹ * 𝔼.E t (fun ω' =>
          (Yh (t + 1) ω' - (Gh (t + 1) ω' + gcoef Ybar Gbar ucc ucxi * xi (t + 1) ω')) -
          (Yh t ω' - (Gh t ω' + gcoef Ybar Gbar ucc ucxi * xi t ω'))) ω +
        𝔼.E t (π (t + 1)) ω) 0 := by
  have hF := hasFDerivAt_lambdaG hY hC hu hcc huc
  obtain ⟨C, r, hr, hrem⟩ := quadratic_remainder (contDiffAt_lambdaG hu huc2)
  rw [hF.fderiv] at hrem
  have hnorm : ∀ s ω', ‖((Yh s ω', Gh s ω', xi s ω') : ℝ × ℝ × ℝ)‖ ≤ K := by
    intro s ω'
    rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (hYb s ω') (max_le (hGb s ω') (hxb s ω'))
  have h := hasDerivAt_neg_log_E_exp 𝔼 hr (lambdaG_zero uc Ybar Gbar) hrem
    (a := fun ω' => (Yh (t + 1) ω', Gh (t + 1) ω', xi (t + 1) ω'))
    (b := fun ω' => (Yh t ω', Gh t ω', xi t ω')) (p := π (t + 1))
    (fun ω' => hnorm (t + 1) ω') (fun ω' => hnorm t ω') (fun ω' => hπb (t + 1) ω') t ω
  refine h.congr_deriv ?_
  set σ := sigmaIS uc Ybar Gbar ucc
  set gc := gcoef Ybar Gbar ucc ucxi
  have hfun : (fun ω' => ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gc • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
          (Yh t ω', Gh t ω', xi t ω') -
      ((-σ⁻¹) • (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
          gc • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))))
          (Yh (t + 1) ω', Gh (t + 1) ω', xi (t + 1) ω') + π (t + 1) ω') =
      σ⁻¹ • (fun ω' => (Yh (t + 1) ω' - (Gh (t + 1) ω' + gc * xi (t + 1) ω')) -
          (Yh t ω' - (Gh t ω' + gc * xi t ω'))) + π (t + 1) := by
    funext ω'
    simp
    ring
  rw [hfun, map_add, map_smul]
  rfl

/-- Woodford (2003), eq. (1.7), p. 243 (**the intertemporal IS relation**):
`Ŷ_t = g_t + E_t(Ŷ_{t+1} − g_{t+1}) − σ(î_t − E_t π_{t+1})` at every date. -/
def IS17 (σ : ℝ) (Yh g ih π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Yh t = g t + 𝔼.E t (Yh (t + 1) - g (t + 1)) - σ • (ih t - 𝔼.E t (π (t + 1)))

/-- Woodford (2003), eq. (1.7), p. 243: setting `î_t` equal to the derivative of `euler_deriv`,
`î_t = σ⁻¹ E_t[(Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t)] + E_t π_{t+1}`, is equivalent to (1.7) when
`Ŷ` and `g` are adapted (`σ ≠ 0`). -/
theorem is17_iff {σ : ℝ} (hσ : σ ≠ 0) {Yh g ih π : ℕ → Ω → ℝ} (hYa : 𝔼.Adapted Yh)
    (hga : 𝔼.Adapted g) :
    (∀ t, ih t = σ⁻¹ • 𝔼.E t ((Yh (t + 1) - g (t + 1)) - (Yh t - g t)) + 𝔼.E t (π (t + 1))) ↔
      IS17 𝔼 σ Yh g ih π := by
  have hE1 : ∀ t ω, 𝔼.E t ((Yh (t + 1) - g (t + 1)) - (Yh t - g t)) ω =
      𝔼.E t (Yh (t + 1)) ω - 𝔼.E t (g (t + 1)) ω - Yh t ω + g t ω := by
    intro t ω
    simp only [map_sub, hYa t, hga t, Pi.sub_apply]
    ring
  have hE2 : ∀ t ω, 𝔼.E t (Yh (t + 1) - g (t + 1)) ω =
      𝔼.E t (Yh (t + 1)) ω - 𝔼.E t (g (t + 1)) ω := by
    intro t ω
    simp only [map_sub, Pi.sub_apply]
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1 ⊢
    rw [hE1] at h1
    rw [hE2]
    field_simp at h1
    linarith
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1 ⊢
    rw [hE2] at h1
    rw [hE1]
    field_simp
    linarith

/-! ### (1.8)–(1.9): the forward solution of the IS relation -/

/-- Woodford (2003), eq. (1.8), p. 244 (iterating (1.7) `k` times): for an adapted interest rate,
`Ŷ_t − g_t = E_t(Ŷ_{t+k} − g_{t+k}) − σ ∑_{j<k} E_t(î_{t+j} − π_{t+j+1})`. -/
theorem is17_iterate {σ : ℝ} {Yh g ih π : ℕ → Ω → ℝ} (hia : 𝔼.Adapted ih)
    (h : IS17 𝔼 σ Yh g ih π) (t k : ℕ) (ω : Ω) :
    Yh t ω - g t ω = 𝔼.E t (Yh (t + k) - g (t + k)) ω -
      σ * ∑ j ∈ Finset.range k, 𝔼.E t (ih (t + j) - π (t + j + 1)) ω := by
  set u : ℕ → Ω → ℝ := fun s => -(σ • (ih s - 𝔼.E s (π (s + 1)))) with hu
  have hua : 𝔼.Adapted u := by
    intro s
    simp only [hu, map_neg, map_smul, map_sub, hia s, 𝔼.E_E_self]
  have hsol : ForwardSolution.Solves 𝔼 1 u (Yh - g) := by
    intro s
    rw [one_smul]
    have := h s
    simp only [hu, Pi.sub_apply]
    funext ω'
    have h' := congrFun this ω'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h' ⊢
    linarith
  have hit := congrFun (ForwardSolution.iterate_A15 𝔼 hua hsol t k) ω
  simp only [one_pow, one_smul, Pi.add_apply, Pi.sub_apply, Finset.sum_apply] at hit
  have hterm : ∀ j, 𝔼.E t (u (t + j)) ω = -(σ * 𝔼.E t (ih (t + j) - π (t + j + 1)) ω) := by
    intro j
    simp only [hu, map_neg, map_smul, map_sub, 𝔼.tower (Nat.le_add_right t j), Pi.neg_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_neg_distrib, ← Finset.mul_sum] at hit
  rw [hit]
  ring

/-- Woodford (2003), eqs. (1.8)–(1.9), p. 244 (**the forward solution of the IS relation, both
directions**): for a solution of (1.7) with adapted `î`, the limit hypothesis (1.9)
`lim_{T→∞} E_t(Ŷ_T − g_T) = Ŷ_∞` holds iff the partial sums converge as in (1.8),
`Ŷ_t = Ŷ_∞ + g_t − σ ∑_{j ≥ 0} E_t(î_{t+j} − π_{t+j+1})` (the series being the limit of its
partial sums; it need not converge absolutely). -/
theorem eq18_iff_eq19 {σ : ℝ} {Yh g ih π : ℕ → Ω → ℝ} (hia : 𝔼.Adapted ih)
    (h : IS17 𝔼 σ Yh g ih π) (Yinf : ℝ) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (Yh T - g T) ω) atTop (𝓝 Yinf) ↔
      Tendsto (fun k => Yinf + g t ω -
        σ * ∑ j ∈ Finset.range k, 𝔼.E t (ih (t + j) - π (t + j + 1)) ω) atTop (𝓝 (Yh t ω)) := by
  have hit := is17_iterate 𝔼 hia h t
  have heq : (fun k => Yinf + g t ω -
      σ * ∑ j ∈ Finset.range k, 𝔼.E t (ih (t + j) - π (t + j + 1)) ω) =
      fun k => Yh t ω + (Yinf - 𝔼.E t (Yh (k + t) - g (k + t)) ω) := by
    funext k
    have := hit k ω
    rw [add_comm k t]
    linarith
  rw [heq, ← tendsto_add_atTop_iff_nat (f := fun T => 𝔼.E t (Yh T - g T) ω) t]
  constructor
  · intro hl
    have := (tendsto_const_nhds (x := Yinf)).sub hl
    simpa using (tendsto_const_nhds (x := Yh t ω)).add this
  · intro hl
    have h2 := (tendsto_const_nhds (x := Yh t ω + Yinf)).sub hl
    simp only [add_sub_cancel_left] at h2
    have h3 : (fun k => Yh t ω + Yinf - (Yh t ω + (Yinf - 𝔼.E t (Yh (k + t) - g (k + t)) ω))) =
        fun k => 𝔼.E t (Yh (k + t) - g (k + t)) ω := by
      funext k; ring
    rw [h3] at h2
    simpa using h2

/-- Woodford (2003), eq. (1.8), p. 244 (with a summable series): under (1.9), if the terms
`E_t(î_{t+j} − π_{t+j+1})` are summable, then
`Ŷ_t = Ŷ_∞ + g_t − σ ∑' j, E_t(î_{t+j} − π_{t+j+1})`. -/
theorem eq18_tsum {σ : ℝ} {Yh g ih π : ℕ → Ω → ℝ} (hia : 𝔼.Adapted ih)
    (h : IS17 𝔼 σ Yh g ih π) {Yinf : ℝ} {t : ℕ} {ω : Ω}
    (h19 : Tendsto (fun T => 𝔼.E t (Yh T - g T) ω) atTop (𝓝 Yinf))
    (hs : Summable (fun j => 𝔼.E t (ih (t + j) - π (t + j + 1)) ω)) :
    Yh t ω = Yinf + g t ω - σ * ∑' j, 𝔼.E t (ih (t + j) - π (t + j + 1)) ω := by
  have h1 := (eq18_iff_eq19 𝔼 hia h Yinf t ω).mp h19
  have h2 : Tendsto (fun k => Yinf + g t ω -
      σ * ∑ j ∈ Finset.range k, 𝔼.E t (ih (t + j) - π (t + j + 1)) ω) atTop
      (𝓝 (Yinf + g t ω - σ * ∑' j, 𝔼.E t (ih (t + j) - π (t + j + 1)) ω)) :=
    tendsto_const_nhds.sub (hs.hasSum.tendsto_sum_nat.const_mul σ)
  exact tendsto_nhds_unique h1 h2

/-- Woodford (2003), p. 244: `(−1)ᵗ` has no limit. -/
theorem not_tendsto_neg_one_pow (L : ℝ) : ¬ Tendsto (fun T : ℕ => (-1 : ℝ) ^ T) atTop (𝓝 L) := by
  intro h
  have he : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    StrictMono.tendsto_atTop (fun a b hab => by omega)
  have ho : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    StrictMono.tendsto_atTop (fun a b hab => by omega)
  have h1 := h.comp he
  have h2 := h.comp ho
  have e1 : ((fun T : ℕ => (-1 : ℝ) ^ T) ∘ fun n : ℕ => 2 * n) = fun _ => 1 := by
    funext n; simp [pow_mul]
  have e2 : ((fun T : ℕ => (-1 : ℝ) ^ T) ∘ fun n : ℕ => 2 * n + 1) = fun _ => -1 := by
    funext n; simp [pow_succ, pow_mul]
  rw [e1] at h1
  rw [e2] at h2
  have := tendsto_nhds_unique h1 tendsto_const_nhds
  have := tendsto_nhds_unique h2 tendsto_const_nhds
  linarith

/-- Woodford (2003), eqs. (1.8)–(1.9), p. 244 (**the limit hypothesis (1.9) is needed**): under
perfect foresight with `σ = 1`, `g = 0`, `π = 0`, the bounded output path `Ŷ_t = (−1)ᵗ` and the
bounded interest rate `î_t = −2(−1)ᵗ` solve (1.7), yet for no `Ŷ_∞` do the partial sums of (1.8)
converge: (1.8) fails because `E_t Ŷ_T` has no limit. -/
theorem eq19_needed :
    ∃ Yh g ih π : ℕ → Unit → ℝ, IS17 perfectForesight 1 Yh g ih π ∧ BoundedProc Yh ∧
      BoundedProc ih ∧ ∀ Yinf : ℝ, ¬ Tendsto (fun k => Yinf + g 0 () -
        1 * ∑ j ∈ Finset.range k, perfectForesight.E 0 (ih (0 + j) - π (0 + j + 1)) ())
        atTop (𝓝 (Yh 0 ())) := by
  set Yh : ℕ → Unit → ℝ := fun t _ => (-1 : ℝ) ^ t with hY
  set ih : ℕ → Unit → ℝ := fun t _ => -2 * (-1 : ℝ) ^ t with hi
  have hIS : IS17 perfectForesight 1 Yh 0 ih 0 := by
    intro t
    funext u
    simp only [hY, hi, perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
      Pi.zero_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    ring
  refine ⟨Yh, 0, ih, 0, hIS, ⟨1, fun t u => by simp [hY]⟩, ⟨2, fun t u => by simp [hi]⟩,
    fun Yinf hT => ?_⟩
  have hia : perfectForesight.Adapted ih := fun t => rfl
  have := (eq18_iff_eq19 perfectForesight hia hIS Yinf 0 ()).mpr hT
  apply not_tendsto_neg_one_pow Yinf
  simpa [hY, perfectForesight] using this

/-- Woodford (2003), fn. 12, p. 244: under (1.9) and `lim_T E_t g_T = 0` ("the long-run average
value of `g_t` is assumed to be zero"), `Ŷ_∞ = lim_T E_t Ŷ_T`. -/
theorem yinf_eq_lim {Yh g : ℕ → Ω → ℝ} {Yinf : ℝ} {t : ℕ} {ω : Ω}
    (h19 : Tendsto (fun T => 𝔼.E t (Yh T - g T) ω) atTop (𝓝 Yinf))
    (hg : Tendsto (fun T => 𝔼.E t (g T) ω) atTop (𝓝 0)) :
    Tendsto (fun T => 𝔼.E t (Yh T) ω) atTop (𝓝 Yinf) := by
  have := h19.add hg
  simp only [add_zero] at this
  refine this.congr fun T => ?_
  simp only [map_sub, Pi.sub_apply]
  ring

/-! ### Footnote 12: the long-run level of output -/

/-- Woodford (2003), fn. 12, p. 244 (**New Keynesian AS relation**): under the NKPC (1.10)
`π_t = κ(Ŷ_t − Ŷⁿ_t) + β E_t π_{t+1}` (`κ ≠ 0`), if `E_t π_T → π_∞`, `E_t Ŷ_T → Ŷ_∞` and
`E_t Ŷⁿ_T → 0`, then `Ŷ_∞ = (1 − β) π_∞ / κ`. -/
theorem fn12_nkpc {β κ : ℝ} (hκ : κ ≠ 0) {π Yh Yn : ℕ → Ω → ℝ}
    (h : ∀ t, π t = κ • (Yh t - Yn t) + β • 𝔼.E t (π (t + 1))) {t : ℕ} {ω : Ω}
    {πinf Yinf : ℝ} (hπ : Tendsto (fun T => 𝔼.E t (π T) ω) atTop (𝓝 πinf))
    (hY : Tendsto (fun T => 𝔼.E t (Yh T) ω) atTop (𝓝 Yinf))
    (hn : Tendsto (fun T => 𝔼.E t (Yn T) ω) atTop (𝓝 0)) :
    Yinf = (1 - β) * πinf / κ := by
  have heq : ∀ᶠ T in atTop, κ * (𝔼.E t (Yh T) ω - 𝔼.E t (Yn T) ω) +
      β * 𝔼.E t (π (T + 1)) ω = 𝔼.E t (π T) ω := by
    filter_upwards [eventually_ge_atTop t] with T hT
    have h1 := congrArg (fun z => 𝔼.E t z ω) (h T)
    simp only [map_add, map_smul, map_sub, 𝔼.tower hT, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul] at h1
    linarith
  have hπ1 : Tendsto (fun T => 𝔼.E t (π (T + 1)) ω) atTop (𝓝 πinf) :=
    hπ.comp (tendsto_add_atTop_nat 1)
  have hR := ((hY.sub hn).const_mul κ).add (hπ1.const_mul β)
  have hlim := tendsto_nhds_unique (hR.congr' heq) hπ
  field_simp
  linarith

/-- Woodford (2003), fn. 12, p. 244, with (1.32) of Chapter 3 (**New Classical AS relation**):
under `π_{t+1} = κ(Ŷ_{t+1} − Ŷⁿ_{t+1}) + E_t π_{t+1}` (`κ ≠ 0`) and `E_t Ŷⁿ_T → 0`, every policy
gives `E_t Ŷ_T → 0`, i.e. `Ŷ_∞ = 0` (no stationarity of inflation is even needed). -/
theorem fn12_newClassical {κ : ℝ} (hκ : κ ≠ 0) {π Yh Yn : ℕ → Ω → ℝ}
    (h : ∀ t, π (t + 1) = κ • (Yh (t + 1) - Yn (t + 1)) + 𝔼.E t (π (t + 1))) {t : ℕ} {ω : Ω}
    (hn : Tendsto (fun T => 𝔼.E t (Yn T) ω) atTop (𝓝 0)) :
    Tendsto (fun T => 𝔼.E t (Yh T) ω) atTop (𝓝 0) := by
  refine hn.congr' ?_
  filter_upwards [eventually_ge_atTop (t + 1)] with T hT
  obtain ⟨s, rfl⟩ : ∃ s, T = s + 1 := ⟨T - 1, by omega⟩
  have hts : t ≤ s := by omega
  have h1 := congrArg (fun z => 𝔼.E t z ω) (h s)
  simp only [map_add, map_smul, map_sub, 𝔼.tower hts, Pi.add_apply, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul] at h1
  have h2 : κ * (𝔼.E t (Yh (s + 1)) ω - 𝔼.E t (Yn (s + 1)) ω) = 0 := by linarith
  have h3 := (mul_eq_zero.mp h2).resolve_left hκ
  linarith

/-- Woodford (2003), p. 244: if `b_k → L` and the partial sums `∑_{k<N} b_k` are bounded, then
`L = 0` (Cesàro). -/
theorem limit_zero_of_bounded_sums {b : ℕ → ℝ} {L R : ℝ} (hb : Tendsto b atTop (𝓝 L))
    (hR : ∀ N, |∑ k ∈ Finset.range N, b k| ≤ R) : L = 0 := by
  have h1 := hb.cesaro
  have h2 : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, b i) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun n : ℕ => (n : ℝ)⁻¹ * R) (fun n => ?_) ?_
    · rw [sub_zero, norm_norm, Real.norm_eq_abs, abs_mul, abs_inv, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hR n) (inv_nonneg.mpr (Nat.cast_nonneg n))
    · simpa using hinv.mul_const R
  exact tendsto_nhds_unique h1 h2

/-- Woodford (2003), fn. 12, p. 244, with (2.36), p. 284, at `γ = 1` (**complete indexation**):
under `π_{t+1} − π_t = κ x_{t+1} + β E_{t+1}(π_{t+2} − π_{t+1})` (`κ ≠ 0`), if inflation is
bounded and `E_t x_T → x_∞`, then `x_∞ = 0`: any policy making inflation stationary (here:
bounded) gives a zero long-run gap. -/
theorem fn12_indexation {β κ M : ℝ} (hκ : κ ≠ 0) {π x : ℕ → Ω → ℝ}
    (h : ∀ t, π (t + 1) - π t = κ • x (t + 1) + β • 𝔼.E (t + 1) (π (t + 2) - π (t + 1)))
    (hπb : ∀ t ω, |π t ω| ≤ M) {t : ℕ} {ω : Ω} {xinf : ℝ}
    (hx : Tendsto (fun T => 𝔼.E t (x T) ω) atTop (𝓝 xinf)) : xinf = 0 := by
  set a : ℕ → ℝ := fun k => 𝔼.E t (π (t + k)) ω with ha
  set b : ℕ → ℝ := fun k => 𝔼.E t (x (t + k + 1)) ω with hb
  have haM : ∀ k, |a k| ≤ M := fun k => 𝔼.abs_E_le (hπb (t + k)) t ω
  have hstep : ∀ k, a (k + 1) - a k = κ * b k + β * (a (k + 2) - a (k + 1)) := by
    intro k
    have h1 := congrArg (fun z => 𝔼.E t z ω) (h (t + k))
    simp only [map_add, map_smul, map_sub, 𝔼.tower (show t ≤ t + k + 1 by omega),
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
    simp only [ha, hb]
    rw [show t + (k + 1) = t + k + 1 by omega, show t + (k + 2) = t + k + 2 by omega]
    linarith
  have hsum : ∀ N, κ * ∑ k ∈ Finset.range N, b k = (a N - a 0) - β * (a (N + 1) - a 1) := by
    intro N
    have e1 : ∑ k ∈ Finset.range N, (a (k + 1) - a k) = a N - a 0 := Finset.sum_range_sub a N
    have e2 : ∑ k ∈ Finset.range N, (a (k + 2) - a (k + 1)) = a (N + 1) - a 1 :=
      Finset.sum_range_sub (fun k => a (k + 1)) N
    have e3 : ∑ k ∈ Finset.range N, (a (k + 1) - a k) =
        κ * ∑ k ∈ Finset.range N, b k + β * ∑ k ∈ Finset.range N, (a (k + 2) - a (k + 1)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => hstep k
    rw [e3, e2] at e1
    linarith
  have hR : ∀ N, |∑ k ∈ Finset.range N, b k| ≤ (2 * M + |β| * (2 * M)) / |κ| := by
    intro N
    rw [le_div_iff₀ (abs_pos.mpr hκ), mul_comm, ← abs_mul, hsum N]
    have h1 : |a N - a 0| ≤ 2 * M := (abs_sub _ _).trans (by linarith [haM N, haM 0])
    have h2 : |β * (a (N + 1) - a 1)| ≤ |β| * (2 * M) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [haM (N + 1), haM 1]))
        (abs_nonneg β)
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hbl : Tendsto b atTop (𝓝 xinf) := by
    have : Tendsto (fun k : ℕ => t + k + 1) atTop atTop :=
      StrictMono.tendsto_atTop (fun p q hpq => by omega)
    exact hx.comp this
  exact limit_zero_of_bounded_sums hbl hR

/-! ### (1.10): the New Keynesian Phillips curve from (1.4)–(1.5)

The log-linearisation of (1.4)–(1.5) and the elimination of `p*_t` is "derived in Section 2 of
Chapter 3" (p. 245). The declarations of this part are restated (copied, with their proofs) from
the Woodford Chapter 3 project (modules `Calvo`, `NKPC`, `QuadraticRoots`): the log Calvo index
(2.5) is the exact derivative of (2.1) (`hasFDerivAt_logIndexFn`), the pricing condition (2.6)
is the vanishing of the exact derivative of (2.4) (`hasDerivAt_focPath`, `eq26_iff_deriv_zero`),
and given (2.5), (2.6) is equivalent to the NKPC (`prop35`). In this chapter's numbering (2.1)
is (1.4), (2.4) is (1.5) and (2.12) is (1.10). -/

/-- Woodford (2003), Ch. 3, eq. (2.13), p. 187: the slope `κ = (1 − α)(1 − αβ)ζ/α` of the New
Keynesian Phillips curve (2.12).
(Restated from the Chapter 3 project.) -/
noncomputable def kappa (α β ζ : ℝ) : ℝ := (1 - α) * (1 - α * β) * ζ / α

/-- Woodford (2003), Ch. 3, eq. (2.3), p. 179: the left-hand side of the first-order condition,
`∑_{k ≥ 0} αᵏ E_t[Q_{t,t+k} Π₁(p, …)]`, where `dprof k ω p` is the marginal profit `Π₁`.
(Restated from the Chapter 3 project.) -/
noncomputable def resetFOC (α : ℝ) (Q : ℕ → Ω → ℝ) (dprof : ℕ → Ω → ℝ → ℝ) (t : ℕ)
    (p : ℝ) : Ω → ℝ :=
  fun ω => ∑' k, α ^ k * 𝔼.E t (fun ω' => Q k ω' * dprof k ω' p) ω

/-! ### Chapter 3, (2.5) as the exact derivative of (2.1) (restated from the Chapter 3 project) -/

/-- Woodford (2003), Ch. 3, eq. (2.1), p. 178, in logs: `log P_t` as a function of `x = log p*_t`
and
`y = log P_{t−1}`, `(1 − θ)⁻¹ log((1 − α) e^{(1−θ)x} + α e^{(1−θ)y})`.
(Restated from the Chapter 3 project.) -/
noncomputable def logIndexFn (α θ x y : ℝ) : ℝ :=
  (1 - θ)⁻¹ * Real.log ((1 - α) * Real.exp ((1 - θ) * x) + α * Real.exp ((1 - θ) * y))

omit 𝔼 in
/-- Woodford (2003), Ch. 3, eq. (2.1), p. 178: if (2.1) holds then
`log P_t = logIndexFn α θ (log p*_t) (log P_{t−1})` exactly (`θ ≠ 1`, positive prices).
(Restated from the Chapter 3 project.) -/
theorem log_calvo_index {α θ P pstar Pprev : ℝ} (hθ : θ ≠ 1) (hP : 0 < P) (hps : 0 < pstar)
    (hPp : 0 < Pprev) (hrec : P ^ (1 - θ) = (1 - α) * pstar ^ (1 - θ) + α * Pprev ^ (1 - θ)) :
    Real.log P = logIndexFn α θ (Real.log pstar) (Real.log Pprev) := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h := congrArg Real.log hrec
  rw [Real.log_rpow hP, Real.rpow_def_of_pos hps, Real.rpow_def_of_pos hPp,
    mul_comm (Real.log pstar), mul_comm (Real.log Pprev)] at h
  rw [logIndexFn, ← h]
  field_simp

omit 𝔼 in
/-- Woodford (2003), Ch. 3, p. 179: on the diagonal (zero inflation, `p*_t = P_{t−1}`),
`logIndexFn α θ x x = x`, i.e. `P_t = p*_t = P_{t−1}`.
(Restated from the Chapter 3 project.) -/
theorem logIndexFn_diag (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) (x : ℝ) : logIndexFn α θ x x = x := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  unfold logIndexFn
  rw [show (1 - α) * Real.exp ((1 - θ) * x) + α * Real.exp ((1 - θ) * x)
      = Real.exp ((1 - θ) * x) by ring, Real.log_exp]
  field_simp

omit 𝔼 in
/-- Woodford (2003), Ch. 3, eq. (2.5), p. 180 (**(2.5) is the exact derivative of (2.1)**): at every
zero-inflation point `(x, x)` the map `(log p*_t, log P_{t−1}) ↦ log P_t` has Fréchet derivative
`(dx, dy) ↦ (1 − α) dx + α dy`, so `log P_t = α log P_{t−1} + (1 − α) log p*_t` to first order.
(Restated from the Chapter 3 project.) -/
theorem hasFDerivAt_logIndexFn (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) (x : ℝ) :
    HasFDerivAt (fun v : ℝ × ℝ => logIndexFn α θ v.1 v.2)
      ((1 - α) • ContinuousLinearMap.fst ℝ ℝ ℝ + α • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, x) := by
  have hsub : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have h1 : HasFDerivAt (fun v : ℝ × ℝ => (1 - θ) * v.1)
      ((1 - θ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (x, x) := hasFDerivAt_fst.const_mul (1 - θ)
  have h2 : HasFDerivAt (fun v : ℝ × ℝ => (1 - θ) * v.2)
      ((1 - θ) • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, x) := hasFDerivAt_snd.const_mul (1 - θ)
  have hs := (h1.exp.const_mul (1 - α)).add (h2.exp.const_mul α)
  have hval : (1 - α) * Real.exp ((1 - θ) * (x, x).1) + α * Real.exp ((1 - θ) * (x, x).2)
      = Real.exp ((1 - θ) * x) := by simp only; ring
  have hne : (1 - α) * Real.exp ((1 - θ) * (x, x).1) + α * Real.exp ((1 - θ) * (x, x).2) ≠ 0 := by
    rw [hval]; exact (Real.exp_pos _).ne'
  have hl := (hs.log hne).const_mul (1 - θ)⁻¹
  refine hl.congr_fderiv ?_
  have hv2 : ((fun y : ℝ × ℝ => (1 - α) * Real.exp ((1 - θ) * y.1))
      + fun y : ℝ × ℝ => α * Real.exp ((1 - θ) * y.2)) (x, x) = Real.exp ((1 - θ) * x) := by
    simp only [Pi.add_apply]; ring
  rw [hv2]
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply,
    Pi.add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  have he := (Real.exp_pos ((1 - θ) * x)).ne'
  field_simp

omit 𝔼 in
/-- Woodford (2003), Ch. 3, eq. (2.5), p. 180, along a path: perturbing `log p*_t = x + s a` and
`log P_{t−1} = x + s b`, `log P_t` has derivative `(1 − α) a + α b` at `s = 0`.
(Restated from the Chapter 3 project.) -/
theorem hasDerivAt_logIndexFn_path (α : ℝ) {θ : ℝ} (hθ : θ ≠ 1) (x a b : ℝ) :
    HasDerivAt (fun s => logIndexFn α θ (x + s * a) (x + s * b)) ((1 - α) * a + α * b) 0 := by
  have hγ : HasDerivAt (fun s : ℝ => (x + s * a, x + s * b)) (a, b) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add x
    · simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add x
  have hF := hasFDerivAt_logIndexFn α hθ x
  have hγ0 : ((fun s : ℝ => (x + s * a, x + s * b)) 0) = (x, x) := by simp
  rw [← hγ0] at hF
  refine (hF.comp_hasDerivAt (0 : ℝ) hγ).congr_deriv ?_
  simp [smul_eq_mul]

/-! ### Chapter 3, (2.6) as the exact derivative of the pricing condition (2.4) -/

omit 𝔼 in
/-- Woodford (2003), Ch. 3, p. 180 (the derivative of the marginal-profit function): writing
`mp(x, y, z) = Π₁(eˣ, eˣ, 1; Ȳ eʸ, z)` (log relative price, log output deviation, disturbance),
a Fréchet derivative `D` of `mp` at the steady state `0` with `mp 0 = 0` gives the uniform
first-order expansion `|mp(sx, sy, sz) − s(ψ_p x + ψ_y y + ψ_z z)| ≤ ε|s|` for bounded
`(x, y, z)`, with `ψ_p = D(1,0,0)`, `ψ_y = D(0,1,0)`, `ψ_z = D(0,0,1)`.
(Restated from the Chapter 3 project.) -/
theorem mp_uniform_expansion {mp : ℝ → ℝ → ℝ → ℝ} {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) D 0) (h0 : mp 0 0 0 = 0)
    {B : ℝ} (hB : 0 ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s x y z : ℝ, |s| < δ → |x| ≤ B → |y| ≤ B → |z| ≤ B →
      |mp (s * x) (s * y) (s * z) - s * (D (1, 0, 0) * x + D (0, 1, 0) * y + D (0, 0, 1) * z)|
        ≤ ε * |s| := by
  have hlo := hD.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlo
  have hε' : 0 < ε / (B + 1) := div_pos hε (by linarith)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.mp (hlo hε')
  refine ⟨δ₀ / (B + 1), div_pos hδ₀ (by linarith), fun s x y z hs hx hy hz => ?_⟩
  have hDv : D (s * x, s * y, s * z)
      = s * (D (1, 0, 0) * x + D (0, 1, 0) * y + D (0, 0, 1) * z) := by
    have : ((s * x, s * y, s * z) : ℝ × ℝ × ℝ)
        = (s * x) • ((1, 0, 0) : ℝ × ℝ × ℝ) + (s * y) • ((0, 1, 0) : ℝ × ℝ × ℝ)
          + (s * z) • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
      ext <;> simp
    rw [this, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  have hnorm : ‖((s * x, s * y, s * z) : ℝ × ℝ × ℝ)‖ ≤ |s| * B := by
    rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul]
    refine max_le (mul_le_mul_of_nonneg_left hx (abs_nonneg s)) (max_le ?_ ?_)
    · exact mul_le_mul_of_nonneg_left hy (abs_nonneg s)
    · exact mul_le_mul_of_nonneg_left hz (abs_nonneg s)
  have hsB : |s| * B < δ₀ := by
    have h1 : |s| * B ≤ |s| * (B + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s)
    have h2 : |s| * (B + 1) < δ₀ := by rwa [lt_div_iff₀ (by linarith)] at hs
    linarith
  have hmem : dist ((s * x, s * y, s * z) : ℝ × ℝ × ℝ) 0 < δ₀ := by
    rw [dist_zero_right]; linarith
  have h := hball hmem
  simp only [h0, sub_zero, Prod.fst_zero, Prod.snd_zero] at h
  rw [Real.norm_eq_abs, hDv] at h
  calc _ ≤ ε / (B + 1) * ‖((s * x, s * y, s * z) : ℝ × ℝ × ℝ)‖ := h
    _ ≤ ε / (B + 1) * (|s| * B) := mul_le_mul_of_nonneg_left hnorm hε'.le
    _ ≤ ε * |s| := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg s]

omit 𝔼 in
/-- Woodford (2003), Ch. 3, p. 180: the stochastic-discount-factor perturbation `e^{s q}`
multiplies a
term that vanishes at the steady state, so it does not affect the first-order expansion:
`|e^{sq} m(s) − s g| ≤ ε|s|` whenever `|m(s) − s g| ≤ ε'|s|`, for bounded `q`, `g`.
(Restated from the Chapter 3 project.) -/
theorem exp_mul_expansion {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ ε' > 0, ∃ δ > 0, ∀ s q g m : ℝ, |s| < δ → |q| ≤ B → |g| ≤ B →
      |m - s * g| ≤ ε' * |s| → |Real.exp (s * q) * m - s * g| ≤ ε * |s| := by
  set E := Real.exp B with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hB
  refine ⟨ε / (2 * E), by positivity, min (1 / (B + 1)) (ε / (4 * (B + 1) ^ 2)),
    lt_min (by positivity) (by positivity), fun s q g m hs hq hg hm => ?_⟩
  have hs1 : |s| < 1 / (B + 1) := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : |s| < ε / (4 * (B + 1) ^ 2) := lt_of_lt_of_le hs (min_le_right _ _)
  have hsB1 : |s| * (B + 1) < 1 := by rwa [lt_div_iff₀ (by linarith)] at hs1
  have hsq1 : |s * q| ≤ |s| * (B + 1) := by
    rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg q]
  have hsq : |s * q| ≤ B := by
    have : |s| ≤ 1 := by nlinarith [abs_nonneg s]
    rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg q]
  have hexp : Real.exp (s * q) ≤ E := Real.exp_le_exp.mpr ((le_abs_self _).trans hsq)
  have hexp1 : |Real.exp (s * q) - 1| ≤ 2 * (|s| * (B + 1)) :=
    (Real.abs_exp_sub_one_le (by linarith)).trans (by linarith)
  have key : Real.exp (s * q) * m - s * g
      = Real.exp (s * q) * (m - s * g) + (Real.exp (s * q) - 1) * (s * g) := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
  have t1 : Real.exp (s * q) * |m - s * g| ≤ E * (ε / (2 * E) * |s|) :=
    mul_le_mul hexp hm (abs_nonneg _) (by linarith)
  have t2 : |Real.exp (s * q) - 1| * (|s| * |g|) ≤ 2 * (|s| * (B + 1)) * (|s| * (B + 1)) := by
    refine mul_le_mul hexp1 (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg s))
      (by positivity) (by positivity)
  have t3 : 2 * (|s| * (B + 1)) * (|s| * (B + 1)) ≤ ε / 2 * |s| := by
    have hB1 : 0 < (B + 1) ^ 2 := by positivity
    have : |s| * (B + 1) ^ 2 ≤ ε / 4 := by
      rw [lt_div_iff₀ (by positivity)] at hs2; linarith
    nlinarith [abs_nonneg s]
  have t1' : E * (ε / (2 * E) * |s|) = ε / 2 * |s| := by field_simp
  linarith

/-- Woodford (2003), Ch. 3, pp. 179–180 (differentiating (2.4) under `E_t` and the infinite sum
at the
steady state): if `gₖ(s) − s g'ₖ = o(s)` uniformly in `k` and the state, and the `g'ₖ` are
uniformly bounded, then `s ↦ ∑ₖ aᵏ E_t[gₖ(s)]` has derivative `∑ₖ aᵏ E_t[g'ₖ]` at `s = 0`
(`0 ≤ a < 1`).
(Restated from the Chapter 3 project.) -/
theorem hasDerivAt_tsum_E_of_expansion {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {g : ℕ → ℝ → Ω → ℝ} {g' : ℕ → Ω → ℝ} {B : ℝ} (hg'b : ∀ k ω, |g' k ω| ≤ B)
    (hexp : ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ k ω, |g k s ω - s * g' k ω| ≤ ε * |s|)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => ∑' k, a ^ k * 𝔼.E t (g k s) ω) (∑' k, a ^ k * 𝔼.E t (g' k) ω) 0 := by
  have hgeo := summable_geometric_of_lt_one ha0 ha1
  -- `g k 0 = 0`
  have hg0 : ∀ k, g k 0 = 0 := by
    intro k
    funext ω'
    obtain ⟨δ, hδ, h⟩ := hexp 1 one_pos
    have := h 0 (by simpa using hδ) k ω'
    simpa using this
  have hF0 : ∑' k, a ^ k * 𝔼.E t (g k 0) ω = 0 := by
    simp [hg0]
  have hsum' : Summable (fun k => a ^ k * 𝔼.E t (g' k) ω) := by
    refine Summable.of_norm_bounded (hgeo.mul_right B) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hg'b k) t ω) (pow_nonneg ha0 k)
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hca : 0 < c * (1 - a) := mul_pos hc (by linarith)
  obtain ⟨δ, hδ, h⟩ := hexp (c * (1 - a)) hca
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
  have hs' : |s| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hs
  have hb : ∀ k ω', |(g k s - s • g' k) ω'| ≤ c * (1 - a) * |s| := fun k ω' => by
    simpa [smul_eq_mul] using h s hs' k ω'
  have hsumd : Summable (fun k => a ^ k * 𝔼.E t (g k s - s • g' k) ω) := by
    refine Summable.of_norm_bounded (hgeo.mul_right (c * (1 - a) * |s|)) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hb k) t ω) (pow_nonneg ha0 k)
  have hsum : Summable (fun k => a ^ k * 𝔼.E t (g k s) ω) := by
    refine (hsumd.add (hsum'.mul_left s)).congr (fun k => ?_)
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hexpr : ∑' k, a ^ k * 𝔼.E t (g k (0 + s)) ω - ∑' k, a ^ k * 𝔼.E t (g k 0) ω
      - s • ∑' k, a ^ k * 𝔼.E t (g' k) ω
      = ∑' k, a ^ k * 𝔼.E t (g k s - s • g' k) ω := by
    rw [zero_add, hF0, sub_zero, smul_eq_mul, ← tsum_mul_left, ← hsum.tsum_sub
      (hsum'.mul_left s)]
    refine tsum_congr fun k => ?_
    rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hexpr, Real.norm_eq_abs, Real.norm_eq_abs]
  have hg2 : Summable (fun k => c * (1 - a) * |s| * a ^ k) := hgeo.mul_left _
  calc |∑' k, a ^ k * 𝔼.E t (g k s - s • g' k) ω|
      ≤ ∑' k, c * (1 - a) * |s| * a ^ k := by
        have hn : |∑' k, a ^ k * 𝔼.E t (g k s - s • g' k) ω|
            ≤ ∑' k, |a ^ k * 𝔼.E t (g k s - s • g' k) ω| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => a ^ k * 𝔼.E t (g k s - s • g' k) ω)
              (by simpa only [Real.norm_eq_abs] using hsumd.abs)
        refine hn.trans (Summable.tsum_le_tsum (fun k => ?_) hsumd.abs hg2)
        rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 k), mul_comm]
        exact mul_le_mul_of_nonneg_right (𝔼.abs_E_le (hb k) t ω) (pow_nonneg ha0 k)
    _ = c * |s| := by
        have h1a : 1 - a ≠ 0 := by linarith
        rw [tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1]
        field_simp

/-- Woodford (2003), Ch. 3, eq. (2.4), p. 179, along a perturbation of the zero-inflation steady
state:
the left-hand side of (2.4) at the state `ω`, when the stochastic discount factor is
`Q_{t,t+k} = βᵏ e^{s q̂ₖ}`, the price index is `log P_{t+k} = lP + s P̂ₖ`, the reset price is
`log p*_t = lP + s p̂*`, log output deviates by `s ŷₖ` and the disturbance is `s ẑₖ`. The
marginal profit is `Π₁(p*, p*, P_{t+k}; Y_{t+k}, ξ̃_{t+k}) = mp(log p* − log P_{t+k}, ŷ, ẑ)` with
`mp(x, y, z) = Π₁(eˣ, eˣ, 1; Ȳ eʸ, z)` (`foc_relative_price`).
(Restated from the Chapter 3 project.) -/
noncomputable def focPath (α β lP : ℝ) (mp : ℝ → ℝ → ℝ → ℝ) (qhat Phat yhat zhat : ℕ → Ω → ℝ)
    (pshat : Ω → ℝ) (t : ℕ) (s : ℝ) (ω : Ω) : ℝ :=
  resetFOC 𝔼 α (fun k ω' => β ^ k * Real.exp (s * qhat k ω'))
    (fun k ω' p => mp (Real.log p - (lP + s * Phat k ω')) (s * yhat k ω') (s * zhat k ω')) t
    (Real.exp (lP + s * pshat ω)) ω

/-- Woodford (2003), Ch. 3, p. 179: at `s = 0` the path is the zero-inflation steady state, where
(2.4)
holds because `Π₁(1, 1, 1; Ȳ, 0) = 0`.
(Restated from the Chapter 3 project.) -/
theorem focPath_zero {α β lP : ℝ} {mp : ℝ → ℝ → ℝ → ℝ} (h0 : mp 0 0 0 = 0)
    (qhat Phat yhat zhat : ℕ → Ω → ℝ) (pshat : Ω → ℝ) (t : ℕ) (ω : Ω) :
    focPath 𝔼 α β lP mp qhat Phat yhat zhat pshat t 0 ω = 0 := by
  simp [focPath, resetFOC, Real.log_exp, h0, 𝔼.const]

/-- Woodford (2003), Ch. 3, eq. (2.6), p. 180 (**the derivative of the first-order condition
(2.4) at the
zero-inflation steady state**). With `0 ≤ α < 1`, `0 ≤ β ≤ 1`, `mp` Fréchet differentiable at
`0` with derivative `D` and `mp 0 = 0`, and all perturbation directions bounded, the left-hand
side of (2.4) has derivative `∑ₖ (αβ)ᵏ E_t[ψ_p (p̂* − P̂ₖ) + ψ_y ŷₖ + ψ_z ẑₖ]` at `s = 0`. The
discount-factor direction `q̂` drops out.
(Restated from the Chapter 3 project.) -/
theorem hasDerivAt_focPath {α β lP : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) {mp : ℝ → ℝ → ℝ → ℝ} {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) D 0) (h0 : mp 0 0 0 = 0)
    {qhat Phat yhat zhat : ℕ → Ω → ℝ} {pshat : Ω → ℝ} {B : ℝ}
    (hq : ∀ k ω, |qhat k ω| ≤ B) (hP : ∀ k ω, |Phat k ω| ≤ B) (hy : ∀ k ω, |yhat k ω| ≤ B)
    (hz : ∀ k ω, |zhat k ω| ≤ B) (hps : ∀ ω, |pshat ω| ≤ B) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => focPath 𝔼 α β lP mp qhat Phat yhat zhat pshat t s ω)
      (∑' k, (α * β) ^ k * 𝔼.E t (fun ω' => D (1, 0, 0) * (pshat ω - Phat k ω')
        + D (0, 1, 0) * yhat k ω' + D (0, 0, 1) * zhat k ω') ω) 0 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hps ω)
  set ψp := D (1, 0, 0)
  set ψy := D (0, 1, 0)
  set ψz := D (0, 0, 1)
  set C := |ψp| + |ψy| + |ψz| with hC
  set Bg := C * (2 * B) + B with hBg
  have hC0 : 0 ≤ C := by positivity
  set g : ℕ → ℝ → Ω → ℝ := fun k s ω' => Real.exp (s * qhat k ω') *
    (β ^ k * mp (s * (pshat ω - Phat k ω')) (s * yhat k ω') (s * zhat k ω')) with hg
  set g' : ℕ → Ω → ℝ := fun k ω' => β ^ k * (ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
    + ψz * zhat k ω') with hg'
  have hxB : ∀ k ω', |pshat ω - Phat k ω'| ≤ 2 * B := fun k ω' =>
    (abs_sub _ _).trans (by linarith [hps ω, hP k ω'])
  have hlin : ∀ k ω', |ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω'|
      ≤ C * (2 * B) := by
    intro k ω'
    have h1 : |ψp * (pshat ω - Phat k ω')| ≤ |ψp| * (2 * B) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hxB k ω') (abs_nonneg _)
    have h2 : |ψy * yhat k ω'| ≤ |ψy| * (2 * B) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by linarith [hy k ω']) (abs_nonneg _)
    have h3 : |ψz * zhat k ω'| ≤ |ψz| * (2 * B) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by linarith [hz k ω']) (abs_nonneg _)
    have h4 := abs_add_le (ψp * (pshat ω - Phat k ω')) (ψy * yhat k ω')
    calc _ ≤ |ψp * (pshat ω - Phat k ω')| + |ψy * yhat k ω'| + |ψz * zhat k ω'| :=
          (abs_add_le _ _).trans (by linarith)
      _ ≤ C * (2 * B) := by rw [hC]; linarith
  have hβk : ∀ k : ℕ, 0 ≤ β ^ k ∧ β ^ k ≤ 1 := fun k => ⟨pow_nonneg hβ0 k, pow_le_one₀ hβ0 hβ1⟩
  have hg'b : ∀ k ω', |g' k ω'| ≤ Bg := by
    intro k ω'
    simp only [hg', abs_mul, abs_of_nonneg (hβk k).1]
    calc β ^ k * |ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω'|
        ≤ 1 * (C * (2 * B)) := mul_le_mul (hβk k).2 (hlin k ω') (abs_nonneg _) zero_le_one
      _ ≤ Bg := by rw [hBg]; linarith
  have hexp : ∀ ε > 0, ∃ δ > 0, ∀ s, |s| < δ → ∀ k ω', |g k s ω' - s * g' k ω'| ≤ ε * |s| := by
    intro ε hε
    have hBg0 : 0 ≤ Bg := by rw [hBg]; positivity
    obtain ⟨ε', hε', δ₁, hδ₁, h1⟩ := exp_mul_expansion hBg0 hε
    obtain ⟨δ₂, hδ₂, h2⟩ := mp_uniform_expansion hD h0 (B := 2 * B) (by linarith) hε'
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs k ω' => ?_⟩
    have hs1 : |s| < δ₁ := lt_of_lt_of_le hs (min_le_left _ _)
    have hs2 : |s| < δ₂ := lt_of_lt_of_le hs (min_le_right _ _)
    have hCB : 0 ≤ C * (2 * B) := by positivity
    have hqk := hq k ω'
    refine h1 s (qhat k ω') (g' k ω') _ hs1 (by rw [hBg]; linarith) (hg'b k ω') ?_
    have hyk := hy k ω'
    have hzk := hz k ω'
    have hm := h2 s (pshat ω - Phat k ω') (yhat k ω') (zhat k ω') hs2 (hxB k ω')
      (by linarith) (by linarith)
    have e : β ^ k * mp (s * (pshat ω - Phat k ω')) (s * yhat k ω') (s * zhat k ω')
        - s * g' k ω' = β ^ k * (mp (s * (pshat ω - Phat k ω')) (s * yhat k ω')
          (s * zhat k ω') - s * (ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
            + ψz * zhat k ω')) := by
      simp only [hg']; ring
    rw [e, abs_mul, abs_of_nonneg (hβk k).1]
    calc β ^ k * |mp (s * (pshat ω - Phat k ω')) (s * yhat k ω') (s * zhat k ω')
          - s * (ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω')|
        ≤ 1 * (ε' * |s|) := mul_le_mul (hβk k).2 hm (abs_nonneg _) zero_le_one
      _ = ε' * |s| := one_mul _
  have hfun : (fun s => focPath 𝔼 α β lP mp qhat Phat yhat zhat pshat t s ω)
      = fun s => ∑' k, α ^ k * 𝔼.E t (g k s) ω := by
    have hk : ∀ k s, (fun ω' => β ^ k * Real.exp (s * qhat k ω') *
        mp (Real.log (Real.exp (lP + s * pshat ω)) - (lP + s * Phat k ω')) (s * yhat k ω')
          (s * zhat k ω')) = g k s := by
      intro k s
      funext ω'
      rw [Real.log_exp, show lP + s * pshat ω - (lP + s * Phat k ω')
        = s * (pshat ω - Phat k ω') by ring]
      simp only [hg]
      ring
    funext s
    simp only [focPath, resetFOC, hk]
  rw [hfun]
  refine (hasDerivAt_tsum_E_of_expansion 𝔼 hα0 hα1 hg'b hexp t ω).congr_deriv ?_
  refine tsum_congr fun k => ?_
  have : g' k = β ^ k • fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
      + ψz * zhat k ω' := by
    funext ω'; simp [hg']
  rw [this, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

omit 𝔼 in
/-- Woodford (2003), Ch. 3, eq. (1.21), p. 154, and p. 157 (the natural rate, linearised
exactly): if
the natural rate of output `ŷⁿ(z)` (in logs, relative to `Ȳ`) solves `Π₁(1, 1, 1; Ȳ e^{ŷⁿ(z)}, z)
= 0` for every disturbance `z`, `ŷⁿ(0) = 0` and `ŷⁿ` has derivative `d` at `0`, then
`ψ_y d + ψ_z = 0`; i.e. `ŷⁿ = −(ψ_z/ψ_y) z` to first order.
(Restated from the Chapter 3 project.) -/
theorem natRate_deriv {mp : ℝ → ℝ → ℝ → ℝ} {D : ℝ × ℝ × ℝ →L[ℝ] ℝ}
    (hD : HasFDerivAt (fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) D 0) {yn : ℝ → ℝ} {d : ℝ}
    (hyn0 : yn 0 = 0) (hyn : HasDerivAt yn d 0) (himp : ∀ z, mp 0 (yn z) z = 0) :
    D (0, 1, 0) * d + D (0, 0, 1) = 0 := by
  have hγ : HasDerivAt (fun z : ℝ => ((0 : ℝ), yn z, z)) ((0 : ℝ), d, (1 : ℝ)) 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hyn.prodMk (hasDerivAt_id (0 : ℝ)))
  have hγ0 : (fun z : ℝ => ((0 : ℝ), yn z, z)) 0 = 0 := by simp [hyn0]
  rw [← hγ0] at hD
  have hc := hD.comp_hasDerivAt (0 : ℝ) hγ
  have hconst : HasDerivAt ((fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) ∘
      fun z : ℝ => ((0 : ℝ), yn z, z)) 0 0 := by
    have : ((fun v : ℝ × ℝ × ℝ => mp v.1 v.2.1 v.2.2) ∘ fun z : ℝ => ((0 : ℝ), yn z, z))
        = fun _ => 0 := by
      funext z; exact himp z
    rw [this]; exact hasDerivAt_const _ _
  have h := hc.unique hconst
  have hlin : ((0 : ℝ), d, (1 : ℝ)) = d • ((0, 1, 0) : ℝ × ℝ × ℝ) + ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hlin, map_add, map_smul, smul_eq_mul] at h
  linarith

omit 𝔼 in
/-- Woodford (2003), Ch. 3, (1.30), p. 158 and (2.6), p. 180: with `ζ = −ψ_y/ψ_p` and the natural
rate
`ŷⁿ = −(ψ_z/ψ_y) z`, the linear marginal profit is `ψ_p x + ψ_y y + ψ_z z = ψ_p (x − ζ(y − ŷⁿ))`.
(Restated from the Chapter 3 project.) -/
theorem marginal_profit_gap_form {ψp ψy : ℝ} (hp : ψp ≠ 0) (hy : ψy ≠ 0) (ψz x y z : ℝ) :
    ψp * x + ψy * y + ψz * z = ψp * (x - (-ψy / ψp) * (y - (-(ψz / ψy) * z))) := by
  field_simp
  ring

/-- Woodford (2003), Ch. 3, eq. (2.6), p. 180 (**(2.6) is the vanishing of the derivative of
(2.4)**):
with `ψ_p ≠ 0`, `ψ_y ≠ 0`, `ζ = −ψ_y/ψ_p` and `ŷⁿ = −(ψ_z/ψ_y) ẑ`, the derivative of
`hasDerivAt_focPath` equals `ψ_p ∑ₖ (αβ)ᵏ E_t[(p̂* − P̂ₖ) − ζ(ŷₖ − ŷⁿₖ)]`, so it vanishes iff
`∑ₖ (αβ)ᵏ E_t[log p*_t − log P_{t+k} − ζ(Ŷ_{t+k} − Ŷⁿ_{t+k})] = 0` to first order.
(Restated from the Chapter 3 project.) -/
theorem focPath_deriv_eq {ψp ψy ψz : ℝ} (hp : ψp ≠ 0) (hy : ψy ≠ 0) (a : ℝ)
    (Phat yhat zhat : ℕ → Ω → ℝ) (pshat : Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑' k, a ^ k * 𝔼.E t (fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
        + ψz * zhat k ω') ω
      = ψp * ∑' k, a ^ k * 𝔼.E t (fun ω' => (pshat ω - Phat k ω')
        - (-ψy / ψp) * (yhat k ω' - (-(ψz / ψy) * zhat k ω'))) ω := by
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have : (fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω' + ψz * zhat k ω')
      = ψp • fun ω' => (pshat ω - Phat k ω') - (-ψy / ψp) * (yhat k ω' - (-(ψz / ψy)
        * zhat k ω')) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    exact marginal_profit_gap_form hp hy _ _ _ _
  rw [this, 𝔼.E_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), Ch. 3, eq. (2.6), p. 180: since `ψ_p ≠ 0`, the derivative of (2.4) vanishes
iff the
log-linear condition (2.6) holds.
(Restated from the Chapter 3 project.) -/
theorem eq26_iff_deriv_zero {ψp ψy ψz : ℝ} (hp : ψp ≠ 0) (hy : ψy ≠ 0) (a : ℝ)
    (Phat yhat zhat : ℕ → Ω → ℝ) (pshat : Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑' k, a ^ k * 𝔼.E t (fun ω' => ψp * (pshat ω - Phat k ω') + ψy * yhat k ω'
        + ψz * zhat k ω') ω = 0 ↔
      ∑' k, a ^ k * 𝔼.E t (fun ω' => (pshat ω - Phat k ω')
        - (-ψy / ψp) * (yhat k ω' - (-(ψz / ψy) * zhat k ω'))) ω = 0 := by
  rw [focPath_deriv_eq 𝔼 hp hy, mul_eq_zero]
  exact ⟨fun h => h.resolve_left hp, Or.inr⟩


/-- Woodford (2003), Ch. 3, eq. (2.6), p. 180 (in levels): the forward sum converges and
`∑_{j ≥ 0} (αβ)ʲ E_t[log p*_t − log P_{t+j} − ζ(Ŷ_{t+j} − Ŷⁿ_{t+j})] = 0`, where
`gap T = ζ(Ŷ_T − Ŷⁿ_T)`.
(Restated from the Chapter 3 project.) -/
def Eq26 (α β : ℝ) (P pstar gap : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable (fun j => (α * β) ^ j *
      𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω') ω) ∧
    ∑' j, (α * β) ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - gap (t + j) ω') ω = 0

/-- Woodford (2003), App. B.3, p. 660 (the bound `|E_t log S_{t+j+1} − E_t log S_{t+j}| ≤ K`):
bounded first differences, `|x_{t+1} − x_t| ≤ K`.
(Restated from the Chapter 3 project.) -/
def BoundedIncr (x : ℕ → Ω → ℝ) : Prop := ∃ K, ∀ t ω, |x (t + 1) ω - x t ω| ≤ K

omit 𝔼 in
/-- Woodford (2003), App. B.3: `∑ j aʲ` converges for `0 ≤ a < 1`.
(Restated from the Chapter 3 project.) -/
theorem summable_nat_mul_geom {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Summable (fun j : ℕ => (j : ℝ) * a ^ j) := by
  have := summable_pow_mul_geometric_of_norm_lt_one 1
    (by rwa [Real.norm_eq_abs, abs_of_nonneg ha0] : ‖a‖ < 1)
  simpa using this

/-- Woodford (2003), Ch. 3, eq. (2.5), p. 180 (in levels, with `P (t + 1) = log P_t`, `P t = log
P_{t−1}`):
`log P_t = α log P_{t−1} + (1 − α) log p*_t` at every date.
(Restated from the Chapter 3 project.) -/
def Eq25 (α : ℝ) (P pstar : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, P (t + 1) ω = α * P t ω + (1 - α) * pstar t ω

omit 𝔼 in
/-- Woodford (2003), Ch. 3, eq. (2.5), p. 180: (2.5) determines the reset price,
`log p*_t = (log P_t − α log P_{t−1})/(1 − α)`.
(Restated from the Chapter 3 project.) -/
theorem pstar_of_eq25 {α : ℝ} (hα1 : α < 1) {P pstar : ℕ → Ω → ℝ} (h25 : Eq25 α P pstar)
    (t : ℕ) : pstar t = fun ω => (P (t + 1) ω - α * P t ω) / (1 - α) := by
  funext ω
  have h1a : 1 - α ≠ 0 := by linarith
  rw [h25 t ω]
  field_simp
  ring

/-! ### The interchange of sums in App. B.4 (restated from the Chapter 3 project) -/

/-- Woodford (2003), App. B.4, p. 662 (**absolute convergence of the double series**): for
`|y_i| ≤ M` and `0 ≤ a < 1`, the double series `∑_{(j,i), i<j} aʲ y_i` converges absolutely.
(Restated from the Chapter 3 project.) -/
theorem summable_double {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ M) :
    Summable (Function.uncurry fun j i : ℕ => if i < j then a ^ j * y i else 0) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hy 0)
  set g : ℕ × ℕ → ℝ := fun p => if p.2 < p.1 then M * a ^ p.1 else 0 with hg
  have hg0 : 0 ≤ g := fun p => by
    simp only [hg, Pi.zero_apply]; split_ifs <;> positivity
  have hrow : ∀ j, ∑' i, g (j, i) = j * (M * a ^ j) := by
    intro j
    rw [tsum_eq_sum (s := Finset.range j) (fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [hg, not_lt.mpr hi])]
    rw [Finset.sum_congr rfl (fun i hi => by
      simp only [Finset.mem_range] at hi; simp [hg, hi] : ∀ i ∈ Finset.range j,
        g (j, i) = M * a ^ j)]
    simp
  have hgs : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun j => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := Finset.range j) (fun i hi => by
        simp only [Finset.mem_range, not_lt] at hi
        simp [hg, not_lt.mpr hi])
    · simp_rw [hrow]
      exact ((summable_nat_mul_geom ha0 ha1).mul_left M).congr fun j => by ring
  refine Summable.of_norm_bounded hgs (fun p => ?_)
  obtain ⟨j, i⟩ := p
  simp only [Function.uncurry_apply_pair, hg, Real.norm_eq_abs]
  split_ifs
  · rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 j), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hy i) (pow_nonneg ha0 j)
  · simp

/-- Woodford (2003), App. B.4, p. 662 (**the interchange of sums**): for `|y_i| ≤ M` and
`0 ≤ a < 1`, `(1 − a) ∑_{j ≥ 0} aʲ ∑_{i<j} y_i = ∑_{i ≥ 0} a^{i+1} y_i` (with
`y_i = E_t π_{t+1+i}` this is
`(1 − αβ) ∑_T (αβ)^{T−t} ∑_{s=t+1}^T π_s = ∑_T (αβ)^{T−t} αβ π_{T+1}`), and the left-hand series
converges.
(Restated from the Chapter 3 project.) -/
theorem interchange_sums {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ M) :
    Summable (fun j => a ^ j * ∑ i ∈ Finset.range j, y i) ∧
      (1 - a) * ∑' j, a ^ j * ∑ i ∈ Finset.range j, y i = ∑' i, a ^ (i + 1) * y i := by
  set f : ℕ → ℕ → ℝ := fun j i => if i < j then a ^ j * y i else 0 with hf
  have hsum := summable_double ha0 ha1 hy
  have hrowval : ∀ j, ∑' i, f j i = a ^ j * ∑ i ∈ Finset.range j, y i := by
    intro j
    rw [tsum_eq_sum (s := Finset.range j) (fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [hf, not_lt.mpr hi]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [hf, hi]
  have hrow : ∀ j, Summable (f j) := fun j =>
    summable_of_ne_finset_zero (s := Finset.range j) (fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [hf, not_lt.mpr hi])
  have h1a : 1 - a ≠ 0 := by linarith
  have hcol : ∀ i, HasSum (fun j => f j i) (a ^ (i + 1) * (1 - a)⁻¹ * y i) := by
    intro i
    have hz : ∑ j ∈ Finset.range (i + 1), f j i = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_range] at hj
      simp [hf, show ¬ i < j by omega]
    have h' : HasSum (fun k => f (k + (i + 1)) i) (a ^ (i + 1) * (1 - a)⁻¹ * y i) := by
      have := (hasSum_geometric_of_lt_one ha0 ha1).mul_left (a ^ (i + 1) * y i)
      convert this using 1
      · funext k
        simp only [hf, show i < k + (i + 1) by omega, ↓reduceIte]
        rw [show k + (i + 1) = (i + 1) + k by omega, pow_add]
        ring
      · ring
    have := (hasSum_nat_add_iff (f := fun j => f j i) (i + 1)).mp h'
    rwa [hz, add_zero] at this
  have hcomm := hsum.tsum_comm' hrow (fun i => (hcol i).summable)
  have hS : Summable (fun j => a ^ j * ∑ i ∈ Finset.range j, y i) := by
    refine Summable.of_norm_bounded ((summable_nat_mul_geom ha0 ha1).mul_left M) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 j)]
    have : |∑ i ∈ Finset.range j, y i| ≤ j * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range j, |y i| ≤ ∑ _i ∈ Finset.range j, M :=
            Finset.sum_le_sum fun i _ => hy i
        _ = j * M := by simp
    calc a ^ j * |∑ i ∈ Finset.range j, y i| ≤ a ^ j * (j * M) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg ha0 j)
      _ = M * (j * a ^ j) := by ring
  refine ⟨hS, ?_⟩
  simp_rw [← hrowval]
  rw [← hcomm, tsum_congr fun i => (hcol i).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  field_simp


/-- Woodford (2003), Ch. 3, §2.2, p. 187: inflation `π_t = log P_t − log P_{t−1}`, in the indexing
`P (t + 1) = log P_t`.
(Restated from the Chapter 3 project.) -/
def infl (P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => P (t + 1) ω - P t ω

/-- Woodford (2003), Ch. 3, eq. (2.12), p. 187 (**the New Keynesian Phillips curve**):
`π_t = κ x_t + β E_t π_{t+1}` at every date.
(Restated from the Chapter 3 project.) -/
def NKPCurve (β κ : ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • x t + β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), App. B.4, p. 662: the expected change in the price index is the sum of
expected inflation, `E_t log P_{t+j} − log P_t = ∑_{i<j} E_t π_{t+1+i}`.
(Restated from the Chapter 3 project.) -/
theorem E_price_change {P : ℕ → Ω → ℝ} (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (t j : ℕ)
    (ω : Ω) :
    𝔼.E t (P (t + j + 1)) ω - P (t + 1) ω
      = ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω := by
  induction j with
  | zero => simp [hpre t]
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : infl P (t + 1 + j) = P (t + (j + 1) + 1) - P (t + j + 1) := by
      funext ω'
      simp only [infl, Pi.sub_apply]
      rw [show t + 1 + j + 1 = t + (j + 1) + 1 by omega, show t + 1 + j = t + j + 1 by omega]
    rw [e, map_sub, Pi.sub_apply]
    ring

/-- Woodford (2003), App. B.4, p. 662 (**(2.6) in terms of inflation**): in the class of bounded
inflation and output gaps, (2.6) holds iff the log relative reset price
`p̂*_t = log p*_t − log P_t` equals `∑_j (αβ)ʲ E_t[αβ π_{t+j+1} + (1 − αβ) ζ x_{t+j}]`.
(Restated from the Chapter 3 project.) -/
theorem eq26_iff_resetGap {α β ζ : ℝ} (hab0 : 0 ≤ α * β) (hab1 : α * β < 1)
    {P pstar x : ℕ → Ω → ℝ} (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1))
    (hps : ∀ t, 𝔼.E t (pstar t) = pstar t) {Mπ Mx : ℝ}
    (hπ : ∀ t ω, |infl P t ω| ≤ Mπ) (hx : ∀ t ω, |x t ω| ≤ Mx) :
    Eq26 𝔼 α β P pstar (fun T ω => ζ * x T ω) ↔
      ∀ t ω, pstar t ω - P (t + 1) ω = ∑' j, (α * β) ^ j *
        (α * β * 𝔼.E t (infl P (t + j + 1)) ω + (1 - α * β) * (ζ * 𝔼.E t (x (t + j)) ω)) := by
  set a := α * β
  have hg := summable_geometric_of_lt_one hab0 hab1
  have h1a : 1 - a ≠ 0 := by linarith
  -- the summand of (2.6)
  have hsummand : ∀ t j ω, 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - ζ * x (t + j) ω') ω
      = (pstar t ω - P (t + 1) ω) - ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω
        - ζ * 𝔼.E t (x (t + j)) ω := by
    intro t j ω
    have hf : (fun ω' => pstar t ω' - P (t + j + 1) ω' - ζ * x (t + j) ω')
        = pstar t - P (t + j + 1) - ζ • x (t + j) := by
      funext ω'; simp [smul_eq_mul]
    rw [hf, map_sub, map_sub, map_smul, hps t]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := E_price_change 𝔼 hpre t j ω
    linarith
  have hEπ : ∀ t i ω, |𝔼.E t (infl P (t + 1 + i)) ω| ≤ Mπ := fun t i ω =>
    𝔼.abs_E_le (hπ (t + 1 + i)) t ω
  have hEx : ∀ t j ω, |ζ * 𝔼.E t (x (t + j)) ω| ≤ |ζ| * Mx := fun t j ω => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hx (t + j)) t ω) (abs_nonneg ζ)
  have key : ∀ t ω,
      Summable (fun j => a ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω'
        - ζ * x (t + j) ω') ω) ∧
      ∑' j, a ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - ζ * x (t + j) ω') ω
        = (1 - a)⁻¹ * ((pstar t ω - P (t + 1) ω) - ∑' j, a ^ j *
          (a * 𝔼.E t (infl P (t + j + 1)) ω + (1 - a) * (ζ * 𝔼.E t (x (t + j)) ω))) := by
    intro t ω
    obtain ⟨hS, hI⟩ := interchange_sums hab0 hab1 (hEπ t · ω)
    have hX : Summable (fun j => a ^ j * (ζ * 𝔼.E t (x (t + j)) ω)) :=
      Summable.of_norm_bounded (hg.mul_right (|ζ| * Mx)) (fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hab0 j)]
        exact mul_le_mul_of_nonneg_left (hEx t j ω) (pow_nonneg hab0 j))
    have hY : Summable (fun i => a ^ (i + 1) * 𝔼.E t (infl P (t + 1 + i)) ω) :=
      Summable.of_norm_bounded ((hg.mul_left a).mul_right Mπ) (fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hab0 _)]
        calc a ^ (i + 1) * |𝔼.E t (infl P (t + 1 + i)) ω| ≤ a ^ (i + 1) * Mπ :=
              mul_le_mul_of_nonneg_left (hEπ t i ω) (pow_nonneg hab0 _)
          _ = a * a ^ i * Mπ := by ring)
    have hsplit : ∀ j, a ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω'
        - ζ * x (t + j) ω') ω = a ^ j * (pstar t ω - P (t + 1) ω)
          - a ^ j * ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω
          - a ^ j * (ζ * 𝔼.E t (x (t + j)) ω) := by
      intro j; rw [hsummand]; ring
    have hS26 := ((hg.mul_right (pstar t ω - P (t + 1) ω)).sub hS).sub hX
    refine ⟨hS26.congr fun j => (hsplit j).symm, ?_⟩
    simp_rw [hsplit]
    rw [Summable.tsum_sub ((hg.mul_right _).sub hS) hX,
      Summable.tsum_sub (hg.mul_right _) hS, tsum_mul_right, tsum_geometric_of_lt_one hab0 hab1]
    have hI' : ∑' j, a ^ j * ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω
        = (1 - a)⁻¹ * ∑' i, a ^ (i + 1) * 𝔼.E t (infl P (t + 1 + i)) ω := by
      rw [← hI]; field_simp
    have hR : ∑' j, a ^ j * (a * 𝔼.E t (infl P (t + j + 1)) ω
        + (1 - a) * (ζ * 𝔼.E t (x (t + j)) ω))
        = ∑' i, a ^ (i + 1) * 𝔼.E t (infl P (t + 1 + i)) ω
          + (1 - a) * ∑' j, a ^ j * (ζ * 𝔼.E t (x (t + j)) ω) := by
      rw [← tsum_mul_left, ← hY.tsum_add (hX.mul_left (1 - a))]
      refine tsum_congr fun j => ?_
      rw [show t + j + 1 = t + 1 + j by omega, pow_succ]
      ring
    rw [hI', hR]
    field_simp
    ring_nf
  constructor
  · intro h t ω
    obtain ⟨-, h0⟩ := h t ω
    rw [(key t ω).2] at h0
    have := (mul_eq_zero.mp h0).resolve_left (inv_ne_zero h1a)
    linarith
  · intro h t ω
    refine ⟨(key t ω).1, ?_⟩
    rw [(key t ω).2, h t ω, sub_self, mul_zero]

/-- Woodford (2003), App. B.4, p. 662: the forcing term of (B.17),
`u_t = αβ E_t π_{t+1} + (1 − αβ) ζ x_t`.
(Restated from the Chapter 3 project.) -/
def resetForcing (a ζ : ℝ) (P x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => a • 𝔼.E t (infl P (t + 1)) + ((1 - a) * ζ) • x t

/-- Woodford (2003), App. B.4, p. 662 (**the recursive form via the tower property**): the forward
sum of (B.4) is `forwardSeries` of the forcing `u`, because `E_t u_{t+j} = αβ E_t π_{t+j+1} +
(1 − αβ)ζ E_t x_{t+j}` by the law of iterated expectations; hence it solves
`p̂*_t = αβ E_t p̂*_{t+1} + u_t` ((B.17)).
(Restated from the Chapter 3 project.) -/
theorem resetGap_rec {a ζ : ℝ} (P x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑' j, a ^ j * (a * 𝔼.E t (infl P (t + j + 1)) ω + (1 - a) * (ζ * 𝔼.E t (x (t + j)) ω))
      = 𝔼.forwardSeries a (resetForcing 𝔼 a ζ P x) t ω := by
  refine tsum_congr fun j => ?_
  simp only [resetForcing, map_add, map_smul, 𝔼.tower (Nat.le_add_right t j), Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), App. B.4, p. 662: `u` is adapted.
(Restated from the Chapter 3 project.) -/
theorem resetForcing_adapted (a ζ : ℝ) {P x : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x) :
    𝔼.Adapted (resetForcing 𝔼 a ζ P x) := by
  intro t
  simp only [resetForcing, map_add, map_smul, 𝔼.E_E_self, hxa t]

/-- Woodford (2003), App. B.4, p. 662: `u` is bounded when inflation and the gap are.
(Restated from the Chapter 3 project.) -/
theorem resetForcing_bounded {a ζ Mπ Mx : ℝ} {P x : ℕ → Ω → ℝ}
    (hπ : ∀ t ω, |infl P t ω| ≤ Mπ) (hx : ∀ t ω, |x t ω| ≤ Mx) :
    ∀ t ω, |resetForcing 𝔼 a ζ P x t ω| ≤ |a| * Mπ + |(1 - a) * ζ| * Mx := by
  intro t ω
  simp only [resetForcing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hπ (t + 1)) t ω) (abs_nonneg a)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx t ω) (abs_nonneg _)

omit 𝔼 in
/-- Woodford (2003), App. B.4, p. 662: (2.5) makes inflation proportional to the log relative
reset price, `π_t = (1 − α)/α · p̂*_t`, i.e. `p̂*_t = α/(1 − α) · π_t`.
(Restated from the Chapter 3 project.) -/
theorem inflation_eq_resetGap {α : ℝ} (hα1 : α < 1) {P pstar : ℕ → Ω → ℝ}
    (h25 : Eq25 α P pstar) (t : ℕ) (ω : Ω) :
    pstar t ω - P (t + 1) ω = α / (1 - α) * infl P t ω := by
  have h1a : 1 - α ≠ 0 := by linarith
  rw [congrFun (pstar_of_eq25 hα1 h25 t) ω]
  simp only [infl]
  field_simp
  ring

omit 𝔼 in
/-- Woodford (2003), App. B.4, p. 662 (the final substitution): with `q = α/(1 − α) π`,
`q_t = αβ E q_{t+1} + αβ Eπ_{t+1} + (1 − αβ)ζ x_t` iff `π_t = κ x_t + β Eπ_{t+1}`.
(Restated from the Chapter 3 project.) -/
theorem B17_iff_nkpc {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (π0 Eπ1 x : ℝ) :
    α / (1 - α) * π0 = α * β * (α / (1 - α) * Eπ1) + (α * β * Eπ1 + (1 - α * β) * ζ * x) ↔
      π0 = kappa α β ζ * x + β * Eπ1 := by
  have h1a : 1 - α ≠ 0 := by linarith
  have key : α / (1 - α) * π0 - (α * β * (α / (1 - α) * Eπ1) + (α * β * Eπ1
      + (1 - α * β) * ζ * x)) = α / (1 - α) * (π0 - (kappa α β ζ * x + β * Eπ1)) := by
    unfold kappa
    field_simp
    ring
  have hc : α / (1 - α) ≠ 0 := div_ne_zero hα0.ne' h1a
  constructor
  · intro h
    have h0 : α / (1 - α) * (π0 - (kappa α β ζ * x + β * Eπ1)) = 0 := by rw [← key, h, sub_self]
    have := (mul_eq_zero.mp h0).resolve_left hc
    linarith
  · intro h
    have : α / (1 - α) * (π0 - (kappa α β ζ * x + β * Eπ1)) = 0 := by rw [h, sub_self, mul_zero]
    rw [← key] at this
    linarith

/-- Woodford (2003), Ch. 3, **Proposition 3.5** (p. 187; App. B.4, pp. 661–662): let `0 < α < 1`,
`0 < β < 1`, let the price index be predetermined (`log P_t` known at `t`) with bounded inflation,
the output gap `x` adapted and bounded, and let (2.5) hold. Then the pricing condition (2.6)
(with `ζ(Ŷ_T − Ŷⁿ_T) = ζ x_T`) holds **if and only if** inflation and the gap satisfy the New
Keynesian Phillips curve (2.12) `π_t = κ x_t + β E_t π_{t+1}`, `κ = (1 − α)(1 − αβ)ζ/α`
(2.13).
(Restated from the Chapter 3 project.) -/
theorem prop35 {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {P pstar x : ℕ → Ω → ℝ} (hPa : ∀ t, 𝔼.E t (P t) = P t)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hπ : BoundedIncr P) (hxa : 𝔼.Adapted x)
    (hxb : BoundedProc x) (h25 : Eq25 α P pstar) :
    Eq26 𝔼 α β P pstar (fun T ω => ζ * x T ω) ↔ NKPCurve 𝔼 β (kappa α β ζ) (infl P) x := by
  obtain ⟨Mπ, hMπ⟩ := hπ
  obtain ⟨Mx, hMx⟩ := hxb
  have hab0 : 0 ≤ α * β := (mul_pos hα0 hβ0).le
  have hab1 : α * β < 1 := by nlinarith
  have hπb : ∀ t ω, |infl P t ω| ≤ Mπ := hMπ
  have h1a : 1 - α ≠ 0 := by linarith
  -- `p*` is known at `t`
  have hps : ∀ t, 𝔼.E t (pstar t) = pstar t := by
    intro t
    rw [pstar_of_eq25 hα1 h25 t]
    have : (fun ω => (P (t + 1) ω - α * P t ω) / (1 - α))
        = (1 - α)⁻¹ • (P (t + 1) - α • P t) := by
      funext ω; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; field_simp
    rw [this, map_smul, map_sub, map_smul, hpre t, hPa t]
  have hiff := eq26_iff_resetGap 𝔼 (ζ := ζ) hab0 hab1 hpre hps hπb hMx
  have hπa : ∀ t, 𝔼.E t (infl P t) = infl P t := by
    intro t
    have : infl P t = P (t + 1) - P t := rfl
    rw [this, map_sub, hpre t, hPa t]
  set u := resetForcing 𝔼 (α * β) ζ P x
  have hub := resetForcing_bounded 𝔼 (a := α * β) (ζ := ζ) hπb hMx
  have hua := resetForcing_adapted 𝔼 (P := P) (α * β) ζ hxa
  -- the reset gap `q = α/(1−α) π`
  set q : ℕ → Ω → ℝ := fun t ω => α / (1 - α) * infl P t ω with hq
  have hqE : ∀ t ω, 𝔼.E t (q (t + 1)) ω = α / (1 - α) * 𝔼.E t (infl P (t + 1)) ω := by
    intro t ω
    have : q (t + 1) = (α / (1 - α)) • infl P (t + 1) := rfl
    rw [this, map_smul]; rfl
  have hstep : ∀ t ω, (q t ω = α * β * 𝔼.E t (q (t + 1)) ω + u t ω) ↔
      infl P t ω = kappa α β ζ * x t ω + β * 𝔼.E t (infl P (t + 1)) ω := by
    intro t ω
    rw [hqE]
    simp only [hq, u, resetForcing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← B17_iff_nkpc hα0 hα1]
  rw [hiff]
  constructor
  · intro h t
    funext ω
    have hq_eq : q = 𝔼.forwardSeries (α * β) u := by
      funext t' ω'
      rw [← resetGap_rec 𝔼 P x t' ω', ← h t' ω', inflation_eq_resetGap hα1 h25 t' ω']
    have hsol := congrFun (𝔼.forwardSeries_solves hab0 hab1 hub hua t) ω
    rw [← hq_eq] at hsol
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsol ⊢
    exact (hstep t ω).mp hsol
  · intro h t ω
    have hqsol : ∀ t, q t = (α * β) • 𝔼.E t (q (t + 1)) + u t := by
      intro t
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (hstep t ω).mpr ?_
      have := congrFun (h t) ω
      simpa [smul_eq_mul] using this
    have hqb : BoundedProc q := ⟨|α / (1 - α)| * Mπ, fun t ω => by
      simp only [hq, abs_mul]
      exact mul_le_mul_of_nonneg_left (hπb t ω) (abs_nonneg _)⟩
    have hq_eq := 𝔼.eq_forwardSeries hab0 hab1 hub hua hqsol hqb
    rw [resetGap_rec 𝔼 P x t ω, ← hq_eq, inflation_eq_resetGap hα1 h25 t ω]



/-! ### (1.10) in this chapter's notation -/

/-- Woodford (2003), eq. (1.10), p. 245 (**the New Keynesian Phillips curve**, derived): with the
log price index predetermined with bounded inflation, the natural rate `Ŷⁿ` and output `Ŷ`
adapted with a bounded gap, and the log-linear (1.4) (`Eq25`), the log-linear pricing condition
(1.5) (`Eq26` with `ζ(Ŷ_T − Ŷⁿ_T)`) holds **iff** `π_t = κ(Ŷ_t − Ŷⁿ_t) + β E_t π_{t+1}` with
`κ = (1 − α)(1 − αβ)ζ/α` (`prop35` with `x = Ŷ − Ŷⁿ`). -/
theorem eq110_iff {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {P pstar Yh Yn : ℕ → Ω → ℝ} (hPa : ∀ t, 𝔼.E t (P t) = P t)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hπ : BoundedIncr P) (hYa : 𝔼.Adapted Yh)
    (hYna : 𝔼.Adapted Yn) (hxb : BoundedProc (fun t ω => Yh t ω - Yn t ω))
    (h25 : Eq25 α P pstar) :
    Eq26 𝔼 α β P pstar (fun T ω => ζ * (Yh T ω - Yn T ω)) ↔
      ∀ t, infl P t = kappa α β ζ • (Yh t - Yn t) + β • 𝔼.E t (infl P (t + 1)) := by
  have hxa : 𝔼.Adapted (fun t ω => Yh t ω - Yn t ω) := by
    intro t
    change 𝔼.E t (Yh t - Yn t) = Yh t - Yn t
    rw [map_sub, hYa t, hYna t]
  exact prop35 𝔼 hα0 hα1 hβ0 hβ1 hPa hpre hπ hxa hxb h25

/-- Woodford (2003), eq. (1.4), p. 240 (**Euler's theorem for the index**): if `𝒫` is homogeneous
of degree one with `𝒫(1, 1) = 1` and has partial derivatives `a`, `b` at `(1, 1)`, then
`a + b = 1`. -/
theorem index_partials_sum {Pagg : ℝ → ℝ → ℝ} (hP : HomogeneousOne Pagg) (h11 : Pagg 1 1 = 1)
    {a b : ℝ} (hd : HasFDerivAt (fun v : ℝ × ℝ => Pagg v.1 v.2)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 1)) :
    a + b = 1 := by
  set γ : ℝ → ℝ × ℝ := fun c => (c, c) with hγdef
  have hγ : HasDerivAt γ ((1 : ℝ), (1 : ℝ)) 1 :=
    (hasDerivAt_id (1 : ℝ)).prodMk (hasDerivAt_id (1 : ℝ))
  have hd' : HasFDerivAt (fun v : ℝ × ℝ => Pagg v.1 v.2)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (γ 1) := hd
  have hc := HasFDerivAt.comp_hasDerivAt (1 : ℝ) hd' hγ
  have hdiag : ∀ᶠ c in 𝓝 (1 : ℝ), ((fun v : ℝ × ℝ => Pagg v.1 v.2) ∘ γ) c = c := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with c hc0
    have := hP c 1 1 hc0 one_pos one_pos
    simp only [mul_one, h11] at this
    simpa using this
  have h1 : HasDerivAt ((fun v : ℝ × ℝ => Pagg v.1 v.2) ∘ γ) 1 1 :=
    (hasDerivAt_id (1 : ℝ)).congr_of_eventuallyEq hdiag
  have := hc.unique h1
  simpa using this

/-- Woodford (2003), eq. (1.4), p. 240 (**the log-linear index law, for any homogeneous `𝒫`**):
under the hypotheses of `index_partials_sum`, and a positive index, at every zero-inflation
point `(x, x)` the map `(log p*_t, log P_{t−1}) ↦ log P_t = log 𝒫(e^{log p*}, e^{log P_{t−1}})`
has derivative `(dx, dy) ↦ a dx + b dy`, where `a + b = 1`; for the Dixit–Stiglitz `𝒫` (fn. 6),
`a = 1 − α` (`hasFDerivAt_logIndexFn`). -/
theorem hasFDerivAt_log_index {Pagg : ℝ → ℝ → ℝ} (hP : HomogeneousOne Pagg)
    (hpos : ∀ p q, 0 < p → 0 < q → 0 < Pagg p q) (h11 : Pagg 1 1 = 1) {a b : ℝ}
    (hd : HasFDerivAt (fun v : ℝ × ℝ => Pagg v.1 v.2)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 1)) (x : ℝ) :
    HasFDerivAt (fun v : ℝ × ℝ => Real.log (Pagg (Real.exp v.1) (Real.exp v.2)))
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, x) := by
  set G : ℝ × ℝ → ℝ := fun w => Real.log (Pagg (Real.exp w.1) (Real.exp w.2)) with hG
  have hshift : (fun v : ℝ × ℝ => Real.log (Pagg (Real.exp v.1) (Real.exp v.2))) =
      fun v => x + G (v - (x, x)) := by
    funext v
    have h := hP (Real.exp x) (Real.exp (v.1 - x)) (Real.exp (v.2 - x)) (Real.exp_pos _)
      (Real.exp_pos _) (Real.exp_pos _)
    rw [← Real.exp_add, ← Real.exp_add, add_sub_cancel, add_sub_cancel] at h
    have hp := hpos (Real.exp (v.1 - x)) (Real.exp (v.2 - x)) (Real.exp_pos _) (Real.exp_pos _)
    simp only [hG, Prod.fst_sub, Prod.snd_sub]
    rw [h, Real.log_mul (Real.exp_pos x).ne' hp.ne', Real.log_exp]
  have he : HasFDerivAt (fun w : ℝ × ℝ => (Real.exp w.1, Real.exp w.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) 0 := by
    have := (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).exp.prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ))).exp
    simpa using this
  have he0 : (fun w : ℝ × ℝ => (Real.exp w.1, Real.exp w.2)) 0 = (1, 1) := by simp
  have hd' : HasFDerivAt (fun v : ℝ × ℝ => Pagg v.1 v.2)
      (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((fun w : ℝ × ℝ => (Real.exp w.1, Real.exp w.2)) 0) := by rw [he0]; exact hd
  have hc := (hd'.comp (0 : ℝ × ℝ) he).log (by simp [h11])
  have hG0 : HasFDerivAt G (a • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
    refine hc.congr_fderiv ?_
    ext <;> simp [h11]
  set tr : ℝ × ℝ → ℝ × ℝ := fun v => v - (x, x) with htrdef
  have htr : HasFDerivAt tr (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (x, x) :=
    (hasFDerivAt_id (x, x)).sub_const (x, x)
  have hG0' : HasFDerivAt G (a • ContinuousLinearMap.fst ℝ ℝ ℝ +
      b • ContinuousLinearMap.snd ℝ ℝ ℝ) (tr (x, x)) := by
    simpa [htrdef] using hG0
  rw [show G = fun v => x + G (tr v) from hshift]
  have := (hG0'.comp (x, x) htr).const_add x
  simpa using this

/-! ### (1.11): the linearised Taylor rule -/

/-- Woodford (2003), eq. (1.6), p. 241, in logs: `(π, π*, Ŷ, ν) ↦ log(β(1 + φ(e^{π − π*}; Ȳ e^Ŷ,
ν)))`, the log deviation of `1 + i_t` from `1 + ī = β⁻¹`. -/
noncomputable def taylorLog (φ : ℝ × ℝ × ℝ → ℝ) (β Ybar : ℝ) (p : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  Real.log (β * (1 + φ (Real.exp (p.1 - p.2.1), Ybar * Real.exp p.2.2.1, p.2.2.2)))

/-- Woodford (2003), eq. (1.11), p. 245 (**(1.11) is the exact derivative of the Taylor rule
(1.6)**): if `φ(1; Ȳ, 0) = β⁻¹ − 1` (zero-inflation steady state) and `φ` has partial
derivatives `φ₁` (in `Π/Π*`), `φ_Y`, `φ_ν` at `(1, Ȳ, 0)`, then `taylorLog` has a Fréchet
derivative `L` at `0` with `L(π, π*, Ŷ, ν) = ī + φ_π(π − π̄) + φ_y Ŷ/4` for every constant
target `π̄`, where `φ_π = βφ₁`, `φ_y = 4βȲφ_Y` and `ī = βφ_ν ν − φ_π(π* − π̄)`. -/
theorem hasFDerivAt_taylorLog {φ : ℝ × ℝ × ℝ → ℝ} {β Ybar φ1 φY φν : ℝ} (hβ : 0 < β)
    (hss : φ (1, Ybar, 0) = β⁻¹ - 1)
    (hφ : HasFDerivAt φ (φ1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
      φY • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
      φν • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
      (1, Ybar, 0)) :
    ∃ L : ℝ × ℝ × ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (taylorLog φ β Ybar) L 0 ∧
      ∀ (πbar : ℝ) (p : ℝ × ℝ × ℝ × ℝ), L p = (β * φν * p.2.2.2 - β * φ1 * (p.2.1 - πbar)) +
        β * φ1 * (p.1 - πbar) + 4 * β * Ybar * φY * p.2.2.1 / 4 := by
  set h : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun p =>
    (Real.exp (p.1 - p.2.1), Ybar * Real.exp p.2.2.1, p.2.2.2) with hh
  have h1 : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.1 - p.2.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ) -
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp
          (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))) 0 :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ))).sub
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ).2)).comp (0 : ℝ × ℝ × ℝ × ℝ)
        (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ))))
  have h2 : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1)
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))) 0 :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ).2.2)).comp (0 : ℝ × ℝ × ℝ × ℝ).2
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ).2))).comp (0 : ℝ × ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ)))
  have h3 : HasFDerivAt (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2)
      (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ × ℝ))) 0 :=
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ).2.2)).comp (0 : ℝ × ℝ × ℝ × ℝ).2
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ).2))).comp (0 : ℝ × ℝ × ℝ × ℝ)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (0 : ℝ × ℝ × ℝ × ℝ)))
  have hd := h1.exp.prodMk ((h2.exp.const_mul Ybar).prodMk h3)
  have h0 : h 0 = (1, Ybar, 0) := by simp [hh]
  have hφ' := hφ
  rw [← h0] at hφ'
  have hval : β * (1 + φ (h 0)) ≠ 0 := by
    rw [h0, hss, add_sub_cancel]
    exact mul_ne_zero hβ.ne' (inv_ne_zero hβ.ne')
  have hcomp := (((hφ'.comp (0 : ℝ × ℝ × ℝ × ℝ) hd).const_add 1).const_mul β).log hval
  refine ⟨_, hcomp, fun πbar p => ?_⟩
  simp [h0, hss]
  field_simp
  ring

/-! ### The gap form (1.12)–(1.15) -/

/-- Woodford (2003), eq. (1.15), p. 246: the natural rate of interest (deviation),
`r̂ⁿ_t = σ⁻¹[(g_t − Ŷⁿ_t) − E_t(g_{t+1} − Ŷⁿ_{t+1})]`. -/
noncomputable def rnHat (σ : ℝ) (g Yn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => σ⁻¹ • ((g t - Yn t) - 𝔼.E t (g (t + 1) - Yn (t + 1)))

/-- Woodford (2003), eq. (1.12), p. 246 (**the IS relation in gap form**):
`x_t = E_t x_{t+1} − σ(î_t − E_t π_{t+1} − r̂ⁿ_t)`. -/
def IS112 (σ : ℝ) (x ih π rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (ih t - 𝔼.E t (π (t + 1)) - rn t)

/-- Woodford (2003), eqs. (1.7), (1.12) and (1.15), p. 246: with the output gap
`x = Ŷ − Ŷⁿ` and `r̂ⁿ` of (1.15), the IS relation (1.7) is equivalent to its gap form (1.12)
(`σ ≠ 0`). -/
theorem is17_iff_is112 {σ : ℝ} (hσ : σ ≠ 0) (Yh g Yn ih π : ℕ → Ω → ℝ) :
    IS17 𝔼 σ Yh g ih π ↔ IS112 𝔼 σ (Yh - Yn) ih π (rnHat 𝔼 σ g Yn) := by
  have key : ∀ t, (Yh - Yn) t - (𝔼.E t ((Yh - Yn) (t + 1)) -
      σ • (ih t - 𝔼.E t (π (t + 1)) - rnHat 𝔼 σ g Yn t)) =
      Yh t - (g t + 𝔼.E t (Yh (t + 1) - g (t + 1)) - σ • (ih t - 𝔼.E t (π (t + 1)))) := by
    intro t
    funext ω
    simp only [rnHat, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub]
    field_simp
    ring
  constructor
  · intro h t
    have := key t
    rw [← h t, sub_self] at this
    exact sub_eq_zero.mp this
  · intro h t
    have := key t
    rw [← h t, sub_self] at this
    exact (sub_eq_zero.mp this.symm)

/-- Woodford (2003), eq. (1.13), p. 246: with `x = Ŷ − Ŷⁿ`, the NKPC (1.10) is
`π_t = κ x_t + β E_t π_{t+1}`. -/
theorem eq110_iff_eq113 (β κ : ℝ) (π Yh Yn : ℕ → Ω → ℝ) :
    (∀ t, π t = κ • (Yh t - Yn t) + β • 𝔼.E t (π (t + 1))) ↔ NKPCurve 𝔼 β κ π (Yh - Yn) :=
  Iff.rfl

/-- Woodford (2003), eqs. (1.11) and (1.14), p. 246 ("this equation describes the same family of
policy rules as (1.11), but the exogenous term `ī_t` is not the same"): the rule
`î_t = ī_t + φ_π(π_t − π̄) + φ_y Ŷ_t/4` is the rule
`î_t = ī'_t + φ_π(π_t − π̄) + φ_x(x_t − x̄)/4` with `φ_x = φ_y`, `x = Ŷ − Ŷⁿ` and the intercept
`ī'_t = ī_t + φ_y(Ŷⁿ_t + x̄)/4`. -/
theorem eq111_iff_eq114 (φπ φy πbar xbar : ℝ) (ibar ih π Yh Yn : ℕ → Ω → ℝ) :
    (∀ t ω, ih t ω = ibar t ω + φπ * (π t ω - πbar) + φy * Yh t ω / 4) ↔
      ∀ t ω, ih t ω = (ibar t ω + φy * (Yn t ω + xbar) / 4) + φπ * (π t ω - πbar) +
        φy * ((Yh t ω - Yn t ω) - xbar) / 4 := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro h <;> rw [h] <;> ring

/-- Woodford (2003), p. 246: the steady-state output gap consistent with the inflation target,
`x̄ = (1 − β)π̄/κ`. -/
noncomputable def xbar (β κ πbar : ℝ) : ℝ := (1 - β) * πbar / κ

/-- Woodford (2003), p. 246: constant inflation `π̄` and a constant gap `x̄'` satisfy (1.13) iff
`x̄' = x̄ = (1 − β)π̄/κ` (`κ ≠ 0`, a nonempty state space). -/
theorem const_nkpc_iff [Nonempty Ω] {β κ : ℝ} (hκ : κ ≠ 0) (πbar xb : ℝ) :
    NKPCurve 𝔼 β κ (fun _ _ => πbar) (fun _ _ => xb) ↔ xb = xbar β κ πbar := by
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hE : ∀ t, 𝔼.E t (fun _ : Ω => πbar) = fun _ => πbar := fun t => 𝔼.const t πbar
  constructor
  · intro h
    have := congrFun (h 0) ω
    simp only [hE, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    unfold xbar
    field_simp
    linarith
  · intro h t
    funext ω'
    simp only [hE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h, xbar]
    field_simp
    ring

/-- Woodford (2003), p. 246 ("in an equilibrium in which the inflation target is achieved on
average, the nominal interest rate `î_t` is on average equal to `ī_t`"): when `π_t = π̄` and
`x_t = x̄`, the rule (1.14) gives `î_t = ī_t`. -/
theorem rule114_at_target (φπ φx πbar xb : ℝ) (ibar : ℝ) :
    ibar + φπ * (πbar - πbar) + φx * (xb - xb) / 4 = ibar := by
  ring

end Woodford.NeoWicksellianFramework.BasicModel
