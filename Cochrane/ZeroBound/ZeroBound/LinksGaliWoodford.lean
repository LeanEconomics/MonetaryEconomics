/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.Links

/-!
# Links with Galí's and Woodford's treatments of the zero bound

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20: §20.1 (pp. 465–469),
§20.2.4 "Forward guidance" (pp. 478–480) and §20.3 (pp. 484–485), compared with Galí (2015),
§5.4 (pp. 144–152) and Woodford (2003), Chapter 6, §4.2 (pp. 427–435) and Proposition 6.3.

## Galí's commitment policy is delayed lift-off plus a glide path (Galí §5.4.2)

Galí's model (restated from the Galí Chapter 5 project): `π_t = βπ_{t+1} + κx_t`,
`x_t = x_{t+1} − σ⁻¹(i_t − π_{t+1} − rⁿ_t)`, natural rate `−η` on `[0, t_Z]` and `ρ > 0` after.

* Zero-rate dynamics are a monotone backward map (`backStep_lt`, `zr_strict`, `zr_le`,
  `zr_lower`): a higher state at a later date gives a strictly higher state at every earlier date
  of a zero-rate spell.
* The discrete delayed-lift-off family `delayPath L` (rate `0` before `L`, the natural rate and
  `x = π = 0` from `L` on; the counterpart of `ForwardGuidance.delayPi`): `delay_isPath`,
  `delay_eq_disc` (lift-off at `t_Z + 1` is Galí's discretionary path), `delay_lt_of_lt`
  (strictly increasing in `L`, the counterpart of `ForwardGuidance.delay_pi0_strictMono`) and
  `delay_pi0_tendsto` (unbounded, the counterpart of `ForwardGuidance.delay_pi0_tendsto`).
* `comm_gt_delay`, `comm_gt_disc`, `comm_rates`: Galí's optimal commitment path (in the form of
  his algorithm, `ZLBCommitment.algorithm_verification`) lies strictly above the delayed-lift-off
  path with the same lift-off date, hence strictly above the discretionary path at EVERY date
  (higher `x_t` and `π_t`), keeps `i = 0 < rⁿ` on `(t_Z, t_C]`, and `comm_loss_lt`: if it is the
  commitment optimum, the discretionary path has strictly larger loss; `comm_loss_lt_alg`: the
  same from the algorithm's conditions alone, via Galí's verification theorem
  `algorithm_verification` (restated with its proof, KKT sufficiency `kkt_sufficient`).
* `xi1_eq`, `xi_pos_iff`, `longrun_price`: the precise condition for `ξ₁,t_C+1 > 0` (price level
  at lift-off below its long-run level `(βσ)⁻¹∑ξ₂ ≥ 0`); `comm_gt_disc_of_state` (dominance on
  the zero-rate spell from a positive lift-off state only); the exact point `cex_optimal`
  (`β = 9/10`, `κ = 1/10`, `ϑ = 1/819`, `σ = 1`, `ρ = 1/10`, `η = 1/100`, `t_Z = 0`), verified
  optimal, with `cex_liftoff_at_shock_end` (`t_C = t_Z`) and `cex_xi_neg` (`ξ₁,1 < 0`, output and
  inflation negative after lift-off): corrections to Galí p. 150.

## The discrete Werning family and forward guidance about `π_T`

* `wState c`: the rate is `0` during the trap and equal to the natural rate afterwards, with the
  bounded post-trap peg continuation `π_{t_Z+1+k} = λ₁⁻ᵏ c` (`λ₁` the root (5.6) of `ZLBPeg`).
  `w_isPath`, `w_bdd`, `w_unique` (**all** bounded paths with this rate path are members:
  a one-parameter family indexed by `c = π_{t_Z+1}`, like `WerningModel.bdd_path_iff`),
  `w_zero` (`c = 0` is Galí's discretionary path, the new-Keynesian selection `π_T = 0`).
* `w_sub`, `w_pi0_sub`: `π_t(c) − π_t(c') = λ₁^{t_Z+1−t}(c − c')`, the discrete
  `ForwardGuidance.dpi_dpiT`; `w_sensitivity_strictMono`, `w_sensitivity_tendsto`; and
  `sensitivity_tendsto_exp`: with period length `t/n`, `λ₁ⁿ → e^{λ^b t}`, the continuous-time
  sensitivity of `ForwardGuidance.dpi0_dpiT`.
* `comm_promise`: the commitment path's date-0 inflation equals that of exactly one member of the
  family, and its promise `c` is strictly positive; `comm_not_member` (if `t_C > t_Z`).

## Woodford's moment constraint versus Cochrane's pathwise bound (Woodford Prop. 6.9)

* `dAvg` (restated from the Woodford Chapter 6 project), `MomentFeasible` ((4.18)–(4.19)) and
  `PathwiseZLB` (`i_t ≥ 0` at every date and state, Cochrane §20.1).
* `pathwise_mean_nonneg`; `band_moment_feasible` (a pathwise band `a ≤ i ≤ b`, `0 ≤ a`,
  `(b − a)² ≤ 4(K − 1)a²` gives Woodford's constraint); `violation_freq_le` (Woodford's
  constraint bounds the discounted frequency of `i < 0` by `(K − 1)/K = 1/(1 + k²)`, a Cantelli
  bound; Cochrane's requires it to be `0`, `pathwise_violation_freq`);
  `pathwise_not_moment`, `moment_not_pathwise`, `neither_implies`: neither constraint implies the
  other (at Woodford's `k = 2.26`).

## The zero-bound steady state and Woodford's welfare loss

* `DispRec` (Woodford's (2.20), restated): at constant inflation `π` the dispersion converges to
  `ZLBWelfare.dispersion α π` (`disp_const_closed`, `disp_const_tendsto`,
  `disp_const_stationary`), and Woodford's discounted dispersion is
  `απ²/((1−α)(1−αβ))` plus a term independent of `π` (`disp_const_discounted`,
  `disp_const_avg`), so `woodford_zlb_better_iff`: Woodford's welfare criterion ranks `Π_L = β`
  above `Π*` iff `1 < βΠ*`, exactly as `ZLBWelfare.zlb_better_iff`.
* `gali_deflation_steady`: Galí's deflationary steady state `π = −ρ`, `i = 0` with `ρ = −log β`
  is Cochrane's `Π_L = β`, with the same output gap; `gali_deflation_worse`: it is strictly worse
  than Galí's target `π = 0`. `quadLoss_steady`: Woodford's quadratic loss at a steady state is
  `ZLBWelfare.ssLoss`.
-/

namespace Cochrane.ZeroBound.LinksGaliWoodford

open Filter Topology
open Cochrane.ZeroBound

/-! ## Galí's zero-bound model (restated from the Galí Chapter 5 project) -/

/-- Galí (2015), p. 145, restated from the Galí Chapter 5 project (`ZLBDiscretion.natRate`);
Cochrane (2023), §20.2.2, p. 474 (the trap): the natural rate, `−η` on `[0, t_Z]`, `ρ` after. -/
noncomputable def natRate (ρ η : ℝ) (tZ t : ℕ) : ℝ := if t ≤ tZ then -η else ρ

/-- Galí (2015), p. 145 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 474: the
natural rate on the shock interval. -/
theorem natRate_of_le {ρ η : ℝ} {tZ t : ℕ} (ht : t ≤ tZ) : natRate ρ η tZ t = -η := by
  simp [natRate, ht]

/-- Galí (2015), p. 145 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 474: the
natural rate after the shock interval. -/
theorem natRate_of_lt {ρ η : ℝ} {tZ t : ℕ} (ht : tZ < t) : natRate ρ η tZ t = ρ := by
  simp [natRate, Nat.not_le.mpr ht]

/-- Galí (2015), eq. (29), p. 145, restated from the Galí Chapter 5 project; Cochrane (2023),
eq. (5.2), p. 118: the deterministic Phillips curve `π_t = βπ_{t+1} + κx_t`. -/
def NKPC (β κ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : Prop := π t = β * π (t + 1) + κ * x t

/-- Galí (2015), eq. (30) and p. 152, restated from the Galí Chapter 5 project; Cochrane (2023),
eq. (5.1), p. 118: the rate implied by the IS curve, `i_t = rⁿ_t + π_{t+1} + σ(x_{t+1} − x_t)`. -/
noncomputable def impliedRate (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  rn t + π (t + 1) + σ * (x (t + 1) - x t)

/-- Galí (2015), p. 146, restated from the Galí Chapter 5 project; Cochrane (2023), §20.1,
p. 467: `υ₁,t = x_{t+1} + (π_{t+1} + rⁿ_t)/σ`, the output gap at which the bound binds. -/
noncomputable def ups1 (σ : ℝ) (rn x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  x (t + 1) + (π (t + 1) + rn t) / σ

/-- Galí (2015), p. 146 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 467: the
implied rate is `σ(υ₁,t − x_t)`. -/
theorem impliedRate_eq {σ : ℝ} (hσ : σ ≠ 0) (rn x π : ℕ → ℝ) (t : ℕ) :
    impliedRate σ rn x π t = σ * (ups1 σ rn x π t - x t) := by
  unfold impliedRate ups1
  field_simp
  ring

/-- Galí (2015), eq. (34), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023),
§20.2.2, p. 475 (the model at a zero rate is a backward recursion): one backward step at a rate
`i_t = rⁿ_t + e`, `(x_t, π_t) = A(x_{t+1}, π_{t+1}) − B e` (`e = η` on a binding bound). -/
noncomputable def backStep (β κ σ e : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 + s.2 / σ - e / σ, κ * s.1 + (β + κ / σ) * s.2 - κ * e / σ)

/-- Galí (2015), eq. (34), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023),
p. 475: `n` backward steps from the terminal state `s_T`. -/
noncomputable def backState (β κ σ η : ℝ) (sT : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => sT
  | n + 1 => backStep β κ σ η (backState β κ σ η sT n)

/-- Galí (2015), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023), p. 475: the
path solving (34) backward on `[0, t_Z]` from `s_T` at `t_Z + 1`, equal to `s_T` after `t_Z`. -/
noncomputable def zlbPath (β κ σ η : ℝ) (tZ : ℕ) (sT : ℝ × ℝ) (t : ℕ) : ℝ × ℝ :=
  if t ≤ tZ then backState β κ σ η sT (tZ + 1 - t) else sT

/-- Galí (2015), eq. (34), p. 147 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 475: on `[0, t_Z]` the path obeys (34). -/
theorem zlbPath_of_le {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : t ≤ tZ) :
    zlbPath β κ σ η tZ sT t = backStep β κ σ η (zlbPath β κ σ η tZ sT (t + 1)) := by
  unfold zlbPath
  have e : tZ + 1 - t = (tZ + 1 - (t + 1)) + 1 := by omega
  simp only [ht, ↓reduceIte, e, backState]
  by_cases h : t + 1 ≤ tZ
  · simp only [h, ↓reduceIte]
  · have e2 : tZ + 1 - (t + 1) = 0 := by omega
    simp only [h, ↓reduceIte, e2, backState]

/-- Galí (2015), p. 147 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 475:
after `t_Z` the path is at its terminal state. -/
theorem zlbPath_of_lt {β κ σ η : ℝ} {tZ t : ℕ} {sT : ℝ × ℝ} (ht : tZ < t) :
    zlbPath β κ σ η tZ sT t = sT := by
  simp [zlbPath, Nat.not_le.mpr ht]

/-- Galí (2015), p. 147, restated from the Galí Chapter 5 project (`ZLBDiscretion.discX`, the
discretionary equilibrium, `disc_exists`/`disc_unique` there); Cochrane (2023), p. 475: the
discretionary output gap, (34) on `[0, t_Z]` from `(0, 0)`, zero afterwards. -/
noncomputable def discX (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).1

/-- Galí (2015), p. 147, restated from the Galí Chapter 5 project; Cochrane (2023), p. 475: the
discretionary inflation path, (34) on `[0, t_Z]` from `(0, 0)`, zero afterwards. -/
noncomputable def discPi (β κ σ η : ℝ) (tZ t : ℕ) : ℝ := (zlbPath β κ σ η tZ (0, 0) t).2

/-- Galí (2015), p. 149, restated from the Galí Chapter 5 project
(`ZLBCommitment.Feasible`); Cochrane (2023), §20.1, p. 465 (the bound `i ≥ 0`): the Phillips
curve and `x_t ≤ υ₁,t` (i.e. `i_t ≥ 0`) at every date. -/
def Feasible (β κ σ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  ∀ t, NKPC β κ x π t ∧ x t ≤ ups1 σ rn x π t

/-- Galí (2015), p. 148, restated from the Galí Chapter 5 project; Cochrane (2023), §20.3,
p. 485: the period loss `β^t (π_t² + ϑ x_t²)`. -/
noncomputable def lossTerm (β ϑ : ℝ) (x π : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t * (π t ^ 2 + ϑ * x t ^ 2)

/-- Galí (2015), p. 148, restated from the Galí Chapter 5 project; Cochrane (2023), p. 485: the
loss `∑ β^t (π_t² + ϑ x_t²)` (a `tsum`; `Optimal` requires summability). -/
noncomputable def loss (β ϑ : ℝ) (x π : ℕ → ℝ) : ℝ := ∑' t, lossTerm β ϑ x π t

/-- Galí (2015), p. 148, restated from the Galí Chapter 5 project
(`ZLBCommitment.Optimal`); Cochrane (2023), §20.2.4, p. 479 (optimal forward guidance): `(x, π)`
solves the commitment problem. -/
def Optimal (β κ σ ϑ : ℝ) (rn x π : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ Summable (lossTerm β ϑ x π) ∧
    ∀ y q, Feasible β κ σ rn y q → Summable (lossTerm β ϑ y q) → loss β ϑ x π ≤ loss β ϑ y q

/-- Galí (2015), p. 149, restated from the Galí Chapter 5 project; Cochrane (2023), p. 479: the
lag with initial condition `ξ₋₁ = 0`. -/
def lag (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => f t

/-- Galí (2015), eq. (36), p. 149, restated from the Galí Chapter 5 project; Cochrane (2023),
p. 479: `ϑ x_t − κ ξ₁,t + ξ₂,t − ξ₂,t−1/β = 0`. -/
def FOC36 (β κ ϑ : ℝ) (x ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  ϑ * x t - κ * ξ1 t + ξ2 t - lag ξ2 t / β = 0

/-- Galí (2015), (14), p. 135, restated from the Galí Chapter 5 project
(`Commitment.gam`); Cochrane (2023), p. 479: `γ = ϑ / (ϑ(1 + β) + κ²)`. -/
noncomputable def gam (β κ ϑ : ℝ) : ℝ := ϑ / (ϑ * (1 + β) + κ ^ 2)

/-- Galí (2015), (15), p. 136, restated from the Galí Chapter 5 project
(`Commitment.del`); Cochrane (2023), p. 479: `δ = (1 − √(1 − 4βγ²)) / (2γβ)`. -/
noncomputable def del (β κ ϑ : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2)) / (2 * gam β κ ϑ * β)

/-- Galí (2015), (14), p. 135 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `γ > 0`. -/
theorem gam_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < gam β κ ϑ := by
  unfold gam; positivity

/-- Galí (2015), (14), p. 135 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `γ(1 + β) ≤ 1`. -/
theorem gam_mul_le {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : gam β κ ϑ * (1 + β) ≤ 1 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_le_one hD]
  nlinarith [sq_nonneg κ]

/-- Galí (2015), (14)–(15), pp. 135–136 (restated from the Galí Chapter 5 project); Cochrane
(2023), p. 479: `γ(1 + β) < 1` iff `κ ≠ 0`. -/
theorem gam_mul_lt_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (1 + β) < 1 ↔ κ ≠ 0 := by
  have hD : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  rw [gam, div_mul_eq_mul_div, div_lt_one hD]
  constructor
  · intro h hκ
    rw [hκ] at h
    linarith
  · intro hκ
    have := pow_pos (abs_pos.2 hκ) 2
    rw [sq_abs] at this
    linarith

/-- Galí (2015), (15), p. 136 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `√(1 − 4βγ²) < 1`. -/
theorem sqrt_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2) < 1 := by
  rw [Real.sqrt_lt' one_pos]
  have := gam_pos (κ := κ) hβ0 hϑ
  have : 0 < 4 * β * gam β κ ϑ ^ 2 := by positivity
  linarith

/-- Galí (2015), (15), p. 136 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `δ > 0`. -/
theorem del_pos {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) : 0 < del β κ ϑ := by
  have := gam_pos (κ := κ) hβ0 hϑ
  have := sqrt_lt_one (κ := κ) hβ0 hϑ
  unfold del
  apply div_pos <;> [linarith; positivity]

/-- Galí (2015), (15), p. 136 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: `δ < 1` iff `κ ≠ 0`. -/
theorem del_lt_one_iff {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    del β κ ϑ < 1 ↔ κ ≠ 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have hiff := gam_mul_lt_iff (κ := κ) hβ0 hϑ
  set g := gam β κ ϑ
  have h0 : 0 ≤ 1 - 2 * g * β := by nlinarith
  have hgb : 0 < g * β := by positivity
  rw [del, div_lt_one (by positivity), ← hiff]
  constructor
  · intro h
    have h1 : 1 - 2 * g * β < Real.sqrt (1 - 4 * β * g ^ 2) := by linarith
    have h2 := (Real.lt_sqrt h0).1 h1
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hgb.le (sub_nonneg.2 hc)]
  · intro h
    have h2 : (1 - 2 * g * β) ^ 2 < 1 - 4 * β * g ^ 2 := by nlinarith
    have := (Real.lt_sqrt h0).2 h2
    linarith

/-- Galí (2015), eq. (42), p. 150, restated from the Galí Chapter 5 project
(`ZLBCommitment.postX`); Cochrane (2023), §20.2.4, p. 479 (the glide path): after lift-off
`x_{t_C+2+k} = κ δ^{k+1} ξ / ϑ`, `ξ = ξ₁,t_C+1`. -/
noncomputable def postX (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := κ * del β κ ϑ ^ (k + 1) * ξ / ϑ

/-- Galí (2015), eq. (43), p. 150, restated from the Galí Chapter 5 project
(`ZLBCommitment.postPi`); Cochrane (2023), p. 479: `π_{t_C+2+k} = (1 − δ) δ^k ξ`. -/
noncomputable def postPi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ :=
  (1 - del β κ ϑ) * del β κ ϑ ^ k * ξ

/-- Galí (2015), eq. (42), p. 150 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: with `ξ > 0` the output gap is positive after lift-off. -/
theorem post_eq42_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hξ : 0 < ξ)
    (k : ℕ) : 0 < postX β κ ϑ ξ k := by
  have := del_pos (κ := κ) hβ hϑ
  unfold postX; positivity

/-- Galí (2015), eq. (43), p. 150 (restated from the Galí Chapter 5 project); Cochrane (2023),
p. 479: with `ξ > 0` inflation is positive after lift-off. -/
theorem post_eq43_pos {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hξ : 0 < ξ) (k : ℕ) : 0 < postPi β κ ϑ ξ k := by
  have h0 := del_pos (κ := κ) hβ hϑ
  have h1 : 0 < 1 - del β κ ϑ := by
    linarith [(del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  unfold postPi; positivity

/-! ## Zero-rate dynamics are a monotone backward map -/

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), §20.2.2, p. 475: a backward step at rate
`i_t = rⁿ_t + e` gives the Phillips curve and that rate (generalising the Galí Chapter 5
project's `backStep_nkpc_rate`, `e = −rⁿ_t`). -/
theorem backStep_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (h : (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1))) :
    NKPC β κ x π t ∧ impliedRate σ rn x π t = rn t + e := by
  rw [Prod.ext_iff] at h
  obtain ⟨hx, hπ⟩ := h
  simp only [backStep] at hx hπ
  refine ⟨?_, ?_⟩
  · unfold NKPC; rw [hπ, hx]; ring
  · unfold impliedRate; rw [hx]; field_simp; ring

/-- Galí (2015), eqs. (29)–(30), p. 145; Cochrane (2023), p. 475: conversely the Phillips curve
and the rate `i_t = rⁿ_t + e` give the backward step. -/
theorem backStep_of_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (hN : NKPC β κ x π t) (hi : impliedRate σ rn x π t = rn t + e) :
    (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1)) := by
  unfold NKPC at hN
  unfold impliedRate at hi
  have hx : x t = x (t + 1) + π (t + 1) / σ - e / σ := by
    have h2 : σ * x t = σ * x (t + 1) + π (t + 1) - e := by linarith
    field_simp
    linarith
  rw [Prod.ext_iff]
  simp only [backStep]
  refine ⟨hx, ?_⟩
  rw [hN, hx]
  ring

/-- Cochrane (2023), §20.2.4, p. 479 (backward induction over a trap of finite length): a
property holding at `N` and propagating from `t + 1` to `t` for `t < N` holds on `[0, N]`. -/
theorem down_ind {P : ℕ → Prop} {N : ℕ} (hN : P N) (hstep : ∀ t, t < N → P (t + 1) → P t) :
    ∀ t, t ≤ N → P t := by
  have key : ∀ n t, t + n = N → P t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      obtain rfl : t = N := by omega
      exact hN
    | succ n ih => intro t ht; exact hstep t (by omega) (ih (t + 1) (by omega))
  intro t ht
  exact key (N - t) t (by omega)

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: the difference of two backward
steps (same forcing), first component: `Δx_t = Δx_{t+1} + Δπ_{t+1}/σ`. -/
theorem backStep_sub_fst (β κ σ e : ℝ) (s s' : ℝ × ℝ) :
    (backStep β κ σ e s).1 - (backStep β κ σ e s').1 = (s.1 - s'.1) + (s.2 - s'.2) / σ := by
  simp only [backStep]; ring

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: the difference of two backward
steps, second component: `Δπ_t = κΔx_{t+1} + (β + κ/σ)Δπ_{t+1}`. -/
theorem backStep_sub_snd (β κ σ e : ℝ) (s s' : ℝ × ℝ) :
    (backStep β κ σ e s).2 - (backStep β κ σ e s').2 =
      κ * (s.1 - s'.1) + (β + κ / σ) * (s.2 - s'.2) := by
  simp only [backStep]; ring

/-- Galí (2015), p. 147 (`A`, `B` entrywise positive); Cochrane (2023), §20.2.4, p. 479 (higher
promised future inflation raises current inflation and output): a weakly higher next state,
strictly higher in one component, gives a strictly higher current state in both. -/
theorem backStep_lt {β κ σ e : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {s s' : ℝ × ℝ}
    (h1 : s'.1 ≤ s.1) (h2 : s'.2 ≤ s.2) (hs : s'.1 < s.1 ∨ s'.2 < s.2) :
    (backStep β κ σ e s').1 < (backStep β κ σ e s).1 ∧
      (backStep β κ σ e s').2 < (backStep β κ σ e s).2 := by
  have e1 := backStep_sub_fst β κ σ e s s'
  have e2 := backStep_sub_snd β κ σ e s s'
  have hc : 0 < β + κ / σ := by positivity
  have ha : 0 ≤ s.1 - s'.1 := by linarith
  have hb : 0 ≤ s.2 - s'.2 := by linarith
  have hbσ : 0 ≤ (s.2 - s'.2) / σ := div_nonneg hb hσ.le
  rcases hs with h | h
  · have ha' : 0 < s.1 - s'.1 := by linarith
    have := mul_pos hκ ha'
    have := mul_nonneg hc.le hb
    constructor <;> linarith
  · have hb' : 0 < s.2 - s'.2 := by linarith
    have := div_pos hb' hσ
    have := mul_pos hc hb'
    have := mul_nonneg hκ.le ha
    constructor <;> linarith

/-- Galí (2015), p. 147; Cochrane (2023), p. 479: a weakly higher next state gives a weakly
higher current state. -/
theorem backStep_le {β κ σ e : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {s s' : ℝ × ℝ}
    (h1 : s'.1 ≤ s.1) (h2 : s'.2 ≤ s.2) :
    (backStep β κ σ e s').1 ≤ (backStep β κ σ e s).1 ∧
      (backStep β κ σ e s').2 ≤ (backStep β κ σ e s).2 := by
  have e1 := backStep_sub_fst β κ σ e s s'
  have e2 := backStep_sub_snd β κ σ e s s'
  have hc : 0 < β + κ / σ := by positivity
  have ha : 0 ≤ s.1 - s'.1 := by linarith
  have hb : 0 ≤ s.2 - s'.2 := by linarith
  have := div_nonneg hb hσ.le
  have := mul_nonneg hκ.le ha
  have := mul_nonneg hc.le hb
  constructor <;> linarith

/-- Cochrane (2023), §20.2.4, p. 479 (discrete form of "promises … have enormous power"):
two paths obeying the same zero-rate backward recursion before `N`, with the state of `p` at `N`
weakly above that of `q` and strictly above in one component, satisfy `q_t < p_t` in both
components at every `t < N`. -/
theorem zr_strict {β κ σ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {e : ℕ → ℝ} {N : ℕ}
    {p q : ℕ → ℝ × ℝ} (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1)))
    (h1 : (q N).1 ≤ (p N).1) (h2 : (q N).2 ≤ (p N).2)
    (hs : (q N).1 < (p N).1 ∨ (q N).2 < (p N).2) (t : ℕ) (ht : t < N) :
    (q t).1 < (p t).1 ∧ (q t).2 < (p t).2 := by
  refine down_ind (P := fun t => t < N → (q t).1 < (p t).1 ∧ (q t).2 < (p t).2)
    (fun h => absurd h (lt_irrefl N)) (fun s hs' ih _ => ?_) t ht.le ht
  rw [hp s hs', hq s hs']
  rcases Nat.lt_or_ge (s + 1) N with h | h
  · obtain ⟨a, b⟩ := ih h
    exact backStep_lt hβ hκ hσ a.le b.le (Or.inl a)
  · obtain rfl : s + 1 = N := by omega
    exact backStep_lt hβ hκ hσ h1 h2 hs

/-- Cochrane (2023), §20.2.4, p. 479: the weak version of `zr_strict`, on `[0, N]`. -/
theorem zr_le {β κ σ : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) {e : ℕ → ℝ} {N : ℕ}
    {p q : ℕ → ℝ × ℝ} (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1)))
    (h1 : (q N).1 ≤ (p N).1) (h2 : (q N).2 ≤ (p N).2) (t : ℕ) (ht : t ≤ N) :
    (q t).1 ≤ (p t).1 ∧ (q t).2 ≤ (p t).2 := by
  refine down_ind (P := fun t => (q t).1 ≤ (p t).1 ∧ (q t).2 ≤ (p t).2) ⟨h1, h2⟩
    (fun s hs ih => ?_) t ht
  rw [hp s hs, hq s hs]
  exact backStep_le hβ hκ hσ ih.1 ih.2

/-- Cochrane (2023), §20.2.4, p. 479: two paths obeying the same zero-rate recursion before `N`
and agreeing at `N` agree on `[0, N]` (the trap path is pinned by its end state). -/
theorem zr_eq {β κ σ : ℝ} {e : ℕ → ℝ} {N : ℕ} {p q : ℕ → ℝ × ℝ}
    (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1))) (hN : p N = q N) (t : ℕ)
    (ht : t ≤ N) : p t = q t := by
  refine down_ind (P := fun t => p t = q t) hN (fun s hs ih => ?_) t ht
  rw [hp s hs, hq s hs, ih]

/-- Cochrane (2023), §20.2.4, p. 479 (quantitative form): if `p` exceeds `q` at `N` by at least
`m ≥ 0` in output and weakly in inflation, then at every `t < N` it exceeds `q` by at least `m` in
output and `κ m` in inflation. -/
theorem zr_lower {β κ σ m : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hm : 0 ≤ m)
    {e : ℕ → ℝ} {N : ℕ} {p q : ℕ → ℝ × ℝ}
    (hp : ∀ t, t < N → p t = backStep β κ σ (e t) (p (t + 1)))
    (hq : ∀ t, t < N → q t = backStep β κ σ (e t) (q (t + 1)))
    (h1 : m ≤ (p N).1 - (q N).1) (h2 : (q N).2 ≤ (p N).2) (t : ℕ) (ht : t < N) :
    m ≤ (p t).1 - (q t).1 ∧ κ * m ≤ (p t).2 - (q t).2 := by
  have hc : 0 < β + κ / σ := by positivity
  have key := down_ind (P := fun t => m ≤ (p t).1 - (q t).1 ∧ 0 ≤ (p t).2 - (q t).2 ∧
      (t < N → κ * m ≤ (p t).2 - (q t).2)) ⟨h1, by linarith, fun h => absurd h (lt_irrefl N)⟩
    (fun s hs ih => by
      obtain ⟨a, b, -⟩ := ih
      have e1 := backStep_sub_fst β κ σ (e s) (p (s + 1)) (q (s + 1))
      have e2 := backStep_sub_snd β κ σ (e s) (p (s + 1)) (q (s + 1))
      rw [← hp s hs, ← hq s hs] at e1 e2
      have := div_nonneg b hσ.le
      have := mul_le_mul_of_nonneg_left a hκ.le
      have := mul_nonneg hc.le b
      have := mul_nonneg hκ.le hm
      exact ⟨by linarith, by linarith, fun _ => by linarith⟩) t ht.le
  exact ⟨key.1, key.2.2 ht⟩

/-- Cochrane (2023), §20.2.4, p. 479: Galí's model is feasible if the Phillips curve holds
and the implied rate is nonnegative at every date (restated from the Galí Chapter 5 project's
`ZLBCommitment.feasible_iff`, one direction). -/
theorem feasible_of_rate {β κ σ : ℝ} (hσ : 0 < σ) {rn x π : ℕ → ℝ}
    (h : ∀ t, NKPC β κ x π t ∧ 0 ≤ impliedRate σ rn x π t) : Feasible β κ σ rn x π := by
  intro t
  refine ⟨(h t).1, ?_⟩
  have := (h t).2
  rw [impliedRate_eq hσ.ne'] at this
  have := (mul_nonneg_iff_of_pos_left hσ).mp this
  linarith

/-! ## Zero-rate paths and the discrete delayed-lift-off family -/

/-- Cochrane (2023), §20.2.4, p. 479: `n` backward zero-rate steps from the state `s_L` at the
lift-off date `L`, with date-dependent forcing `e` (the step from `L − n` to `L − n − 1`). -/
noncomputable def zrAux (β κ σ : ℝ) (e : ℕ → ℝ) (L : ℕ) (sL : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => sL
  | n + 1 => backStep β κ σ (e (L - (n + 1))) (zrAux β κ σ e L sL n)

/-- Cochrane (2023), §20.2.4, p. 479: the path that solves the backward recursion with forcing
`e` before `L` and sits at `s_L` from `L` on. -/
noncomputable def zrPath (β κ σ : ℝ) (e : ℕ → ℝ) (L : ℕ) (sL : ℝ × ℝ) (t : ℕ) : ℝ × ℝ :=
  if L ≤ t then sL else zrAux β κ σ e L sL (L - t)

/-- Cochrane (2023), §20.2.4, p. 479: before `L` the path obeys the backward recursion. -/
theorem zrPath_of_lt {β κ σ : ℝ} {e : ℕ → ℝ} {L t : ℕ} {sL : ℝ × ℝ} (ht : t < L) :
    zrPath β κ σ e L sL t = backStep β κ σ (e t) (zrPath β κ σ e L sL (t + 1)) := by
  unfold zrPath
  have h1 : ¬ L ≤ t := by omega
  have e1 : L - t = (L - (t + 1)) + 1 := by omega
  have e2 : L - (L - (t + 1) + 1) = t := by omega
  simp only [h1, ↓reduceIte, e1, zrAux, e2]
  by_cases h : L ≤ t + 1
  · have e3 : L - (t + 1) = 0 := by omega
    simp only [h, ↓reduceIte, e3, zrAux]
  · simp only [h, ↓reduceIte]

/-- Cochrane (2023), §20.2.4, p. 479: from `L` on the path is at `s_L`. -/
theorem zrPath_of_ge {β κ σ : ℝ} {e : ℕ → ℝ} {L t : ℕ} {sL : ℝ × ℝ} (ht : L ≤ t) :
    zrPath β κ σ e L sL t = sL := by
  simp [zrPath, ht]

/-- Cochrane (2023), §20.2.4, p. 479 (delayed lift-off, Woodford 2012, Werning 2012), in Galí's
discrete model: the rate is `0` before the lift-off date `L` and equal to the natural rate from
`L` on, with `x = π = 0` from `L` on (the discrete counterpart of `ForwardGuidance.delayPi`,
whose `π_L = 0`). -/
noncomputable def delayPath (β κ σ ρ η : ℝ) (tZ L : ℕ) : ℕ → ℝ × ℝ :=
  zrPath β κ σ (fun t => -natRate ρ η tZ t) L (0, 0)

/-- Cochrane (2023), §20.2.4, p. 479: before lift-off the delayed path obeys the zero-rate
recursion. -/
theorem delay_step {β κ σ ρ η : ℝ} {tZ L t : ℕ} (ht : t < L) :
    delayPath β κ σ ρ η tZ L t =
      backStep β κ σ (-natRate ρ η tZ t) (delayPath β κ σ ρ η tZ L (t + 1)) :=
  zrPath_of_lt ht

/-- Cochrane (2023), §20.2.4, p. 479: from lift-off on, `x = π = 0`. -/
theorem delay_after {β κ σ ρ η : ℝ} {tZ L t : ℕ} (ht : L ≤ t) :
    delayPath β κ σ ρ η tZ L t = (0, 0) :=
  zrPath_of_ge ht

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.delay_isPath`, discrete): the delayed
lift-off path satisfies the Phillips curve at every date, has `i_t = 0` before `L` and
`i_t = ρ = rⁿ_t` from `L ≥ t_Z + 1` on; with `ρ ≥ 0` it is feasible (`i ≥ 0`). -/
theorem delay_isPath {β κ σ ρ η : ℝ} (hσ : 0 < σ) {tZ L : ℕ} (hL : tZ + 1 ≤ L) :
    (∀ t, NKPC β κ (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t) ∧
      (∀ t, t < L → impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = 0) ∧
      (∀ t, L ≤ t → impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = ρ) := by
  have hlt : ∀ t, t < L → NKPC β κ (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = 0 := by
    intro t ht
    have h := backStep_rate (rn := natRate ρ η tZ) (x := fun s => (delayPath β κ σ ρ η tZ L s).1)
      (π := fun s => (delayPath β κ σ ρ η tZ L s).2) (t := t) hσ.ne' (delay_step ht)
    exact ⟨h.1, by rw [h.2]; ring⟩
  have hge : ∀ t, L ≤ t → NKPC β κ (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
        (fun s => (delayPath β κ σ ρ η tZ L s).2) t = ρ := by
    intro t ht
    have a := delay_after (β := β) (κ := κ) (σ := σ) (ρ := ρ) (η := η) (tZ := tZ) ht
    have b := delay_after (β := β) (κ := κ) (σ := σ) (ρ := ρ) (η := η) (tZ := tZ)
      (show L ≤ t + 1 by omega)
    refine ⟨?_, ?_⟩
    · simp only [NKPC, a, b]; ring
    · simp only [impliedRate, a, b, natRate_of_lt (show tZ < t by omega)]; ring
  refine ⟨fun t => ?_, fun t ht => (hlt t ht).2, fun t ht => (hge t ht).2⟩
  rcases Nat.lt_or_ge t L with h | h
  · exact (hlt t h).1
  · exact (hge t h).1

/-- Cochrane (2023), §20.2.4, p. 479: with `ρ ≥ 0` the delayed lift-off path is feasible in
Galí's sense (Phillips curve and `i ≥ 0`). -/
theorem delay_feasible {β κ σ ρ η : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) {tZ L : ℕ}
    (hL : tZ + 1 ≤ L) :
    Feasible β κ σ (natRate ρ η tZ) (fun s => (delayPath β κ σ ρ η tZ L s).1)
      (fun s => (delayPath β κ σ ρ η tZ L s).2) := by
  obtain ⟨h1, h2, h3⟩ := delay_isPath (β := β) (κ := κ) (ρ := ρ) (η := η) hσ hL
  refine feasible_of_rate hσ fun t => ⟨h1 t, ?_⟩
  rcases Nat.lt_or_ge t L with h | h
  · rw [h2 t h]
  · rw [h3 t h]; exact hρ

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), p. 147: lift-off at the end of the shock,
`L = t_Z + 1`, is Galí's discretionary path (`discX`, `discPi`): the new-Keynesian selection
"rates rise as soon as the natural rate does, with no promised inflation". -/
theorem delay_eq_disc (β κ σ ρ η : ℝ) (tZ t : ℕ) :
    delayPath β κ σ ρ η tZ (tZ + 1) t = zlbPath β κ σ η tZ (0, 0) t := by
  rcases Nat.lt_or_ge tZ t with h | h
  · rw [delay_after (by omega), zlbPath_of_lt h]
  · refine zr_eq (e := fun t => -natRate ρ η tZ t) (N := tZ + 1)
      (fun s hs => delay_step hs) (fun s hs => ?_) ?_ t (by omega)
    · rw [natRate_of_le (by omega : s ≤ tZ), neg_neg]
      exact zlbPath_of_le (by omega)
    · rw [delay_after le_rfl, zlbPath_of_lt (by omega)]

/-- Cochrane (2023), §20.2.4, p. 479 ("a policy that commits to delaying an interest-rate rise",
discrete): postponing lift-off by one period, from `L ≥ t_Z + 1` to `L + 1`, raises output and
inflation strictly at every date `t ≤ L` and leaves them unchanged after. -/
theorem delay_succ {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ L : ℕ} (hL : tZ + 1 ≤ L) :
    (∀ t, t ≤ L → (delayPath β κ σ ρ η tZ L t).1 < (delayPath β κ σ ρ η tZ (L + 1) t).1 ∧
      (delayPath β κ σ ρ η tZ L t).2 < (delayPath β κ σ ρ η tZ (L + 1) t).2) ∧
    ∀ t, (delayPath β κ σ ρ η tZ L t).1 ≤ (delayPath β κ σ ρ η tZ (L + 1) t).1 ∧
      (delayPath β κ σ ρ η tZ L t).2 ≤ (delayPath β κ σ ρ η tZ (L + 1) t).2 := by
  have hL0 : delayPath β κ σ ρ η tZ L L = (0, 0) := delay_after le_rfl
  have hL1 : delayPath β κ σ ρ η tZ (L + 1) L = (ρ / σ, κ * ρ / σ) := by
    rw [delay_step (by omega), delay_after le_rfl, natRate_of_lt (by omega)]
    simp only [backStep]
    ext <;> simp only <;> ring
  have hpos : 0 < ρ / σ := div_pos hρ hσ
  have hpos2 : 0 < κ * ρ / σ := by positivity
  have hstrict : ∀ t, t ≤ L → (delayPath β κ σ ρ η tZ L t).1 <
      (delayPath β κ σ ρ η tZ (L + 1) t).1 ∧
      (delayPath β κ σ ρ η tZ L t).2 < (delayPath β κ σ ρ η tZ (L + 1) t).2 := by
    intro t ht
    rcases Nat.lt_or_ge t L with h | h
    · refine zr_strict hβ hκ hσ (e := fun t => -natRate ρ η tZ t) (N := L)
        (fun s hs => delay_step (by omega)) (fun s hs => delay_step hs) ?_ ?_ ?_ t h
      · rw [hL0, hL1]; exact hpos.le
      · rw [hL0, hL1]; exact hpos2.le
      · rw [hL0, hL1]; exact Or.inl hpos
    · obtain rfl : t = L := by omega
      rw [hL0, hL1]
      exact ⟨hpos, hpos2⟩
  refine ⟨hstrict, fun t => ?_⟩
  rcases Nat.lt_or_ge L t with h | h
  · rw [delay_after h.le, delay_after (by omega)]
    exact ⟨le_rfl, le_rfl⟩
  · exact ⟨(hstrict t h).1.le, (hstrict t h).2.le⟩

/-- Cochrane (2023), §20.2.4, p. 479: a later lift-off gives a weakly higher path at every
date. -/
theorem delay_le_of_le {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ L1 L2 : ℕ} (hL1 : tZ + 1 ≤ L1) (h12 : L1 ≤ L2) (t : ℕ) :
    (delayPath β κ σ ρ η tZ L1 t).1 ≤ (delayPath β κ σ ρ η tZ L2 t).1 ∧
      (delayPath β κ σ ρ η tZ L1 t).2 ≤ (delayPath β κ σ ρ η tZ L2 t).2 := by
  obtain ⟨n, rfl⟩ : ∃ n, L2 = L1 + n := ⟨L2 - L1, by omega⟩
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have h := (delay_succ (η := η) hβ hκ hσ hρ (tZ := tZ) (L := L1 + n) (by omega)).2 t
    rw [← add_assoc]
    exact ⟨(ih (by omega)).1.trans h.1, (ih (by omega)).2.trans h.2⟩

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.delay_pi0_strictMono`, discrete):
**output and inflation are strictly increasing in the lift-off date** at every date before the
later lift-off. -/
theorem delay_lt_of_lt {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ L1 L2 t : ℕ} (hL1 : tZ + 1 ≤ L1) (h12 : L1 < L2) (ht : t < L2) :
    (delayPath β κ σ ρ η tZ L1 t).1 < (delayPath β κ σ ρ η tZ L2 t).1 ∧
      (delayPath β κ σ ρ η tZ L1 t).2 < (delayPath β κ σ ρ η tZ L2 t).2 := by
  obtain ⟨L, rfl⟩ : ∃ L, L2 = L + 1 := ⟨L2 - 1, by omega⟩
  have a := delay_le_of_le (η := η) hβ hκ hσ hρ hL1 (show L1 ≤ L by omega) t
  have b := (delay_succ (η := η) hβ hκ hσ hρ (tZ := tZ) (L := L) (by omega)).1 t (by omega)
  exact ⟨a.1.trans_lt b.1, a.2.trans_lt b.2⟩

/-- Cochrane (2023), §20.2.4, p. 479: between the end of the shock and lift-off (rate `0`
below the natural rate `ρ`), output is at least `(L − t)ρ/σ` and inflation is nonnegative. -/
theorem delay_growth {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    {tZ L t : ℕ} (htZ : tZ + 1 ≤ t) (htL : t ≤ L) :
    ((L : ℝ) - t) * ρ / σ ≤ (delayPath β κ σ ρ η tZ L t).1 ∧
      0 ≤ (delayPath β κ σ ρ η tZ L t).2 := by
  have hc : 0 < β + κ / σ := by positivity
  refine down_ind (N := L) (P := fun t => tZ + 1 ≤ t → ((L : ℝ) - t) * ρ / σ ≤
      (delayPath β κ σ ρ η tZ L t).1 ∧ 0 ≤ (delayPath β κ σ ρ η tZ L t).2)
    (fun _ => by rw [delay_after le_rfl]; simp) (fun s hs ih hs1 => ?_) t htL htZ
  obtain ⟨a, b⟩ := ih (by omega)
  rw [delay_step hs, natRate_of_lt (by omega)]
  simp only [backStep]
  have hm : 0 ≤ ((L : ℝ) - ((s + 1 : ℕ) : ℝ)) * ρ / σ := by
    have : ((s + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hs
    have : 0 ≤ (L : ℝ) - ((s + 1 : ℕ) : ℝ) := by linarith
    positivity
  have e : ((L : ℝ) - s) * ρ / σ = ((L : ℝ) - ((s + 1 : ℕ) : ℝ)) * ρ / σ + ρ / σ := by
    push_cast; ring
  have h1 := div_nonneg b hσ.le
  have h2 := mul_nonneg hκ.le (hm.trans a)
  have h3 := mul_nonneg hc.le b
  have h4 : 0 ≤ κ * ρ / σ := by positivity
  constructor
  · rw [e]
    have : -(ρ / σ) = -ρ / σ := by ring
    linarith
  · have : -(κ * -ρ / σ) = κ * ρ / σ := by ring
    linarith

/-- Cochrane (2023), §20.2.4, p. 479 (discrete form of `ForwardGuidance.delay_pi0_tendsto`):
with lift-off at `L ≥ t_Z + 1`, date-0 inflation exceeds the discretionary one by at least
`κ(L − t_Z − 1)ρ/σ`, and output by at least `(L − t_Z − 1)ρ/σ`. -/
theorem delay_lower {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    {tZ L : ℕ} (hL : tZ + 1 ≤ L) :
    discX β κ σ η tZ 0 + ((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ ≤ (delayPath β κ σ ρ η tZ L 0).1 ∧
      discPi β κ σ η tZ 0 + κ * (((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ) ≤
        (delayPath β κ σ ρ η tZ L 0).2 := by
  have hm : 0 ≤ ((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ := by
    have : ((tZ + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hL
    have : 0 ≤ (L : ℝ) - (tZ + 1 : ℕ) := by linarith
    positivity
  have hg := delay_growth (β := β) (η := η) hβ hκ hσ hρ (t := tZ + 1) le_rfl hL
  have hd : delayPath β κ σ ρ η tZ (tZ + 1) (tZ + 1) = (0, 0) := delay_after le_rfl
  have h := zr_lower hβ hκ hσ hm (e := fun t => -natRate ρ η tZ t) (N := tZ + 1)
    (p := delayPath β κ σ ρ η tZ L) (q := delayPath β κ σ ρ η tZ (tZ + 1))
    (fun s hs => delay_step (by omega)) (fun s hs => delay_step hs)
    (by rw [hd]; simpa using hg.1) (by rw [hd]; exact hg.2) 0 (by omega)
  rw [delay_eq_disc] at h
  exact ⟨by unfold discX; linarith [h.1], by unfold discPi; linarith [h.2]⟩

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.delay_pi0_tendsto`, discrete): **a long
enough delay produces any initial inflation** — date-0 inflation tends to `+∞` as the lift-off
date `L → ∞` (`ρ > 0`). -/
theorem delay_pi0_tendsto {β κ σ ρ η : ℝ} (hβ : 0 ≤ β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    (tZ : ℕ) : Tendsto (fun L : ℕ => (delayPath β κ σ ρ η tZ L 0).2) atTop atTop := by
  set c := discPi β κ σ η tZ 0 - κ * ((tZ + 1 : ℕ) : ℝ) * ρ / σ
  have hk : 0 < κ * ρ / σ := by positivity
  have hE : Tendsto (fun L : ℕ => c + κ * ρ / σ * (L : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop c (tendsto_natCast_atTop_atTop.const_mul_atTop hk)
  refine tendsto_atTop_mono' atTop ?_ hE
  filter_upwards [eventually_ge_atTop (tZ + 1)] with L hL
  have := (delay_lower (η := η) hβ hκ hσ hρ.le hL).2
  have e : c + κ * ρ / σ * (L : ℝ) = discPi β κ σ η tZ 0 +
      κ * (((L : ℝ) - (tZ + 1 : ℕ)) * ρ / σ) := by
    simp only [c]; ring
  rw [e]
  exact this

/-! ## Galí's commitment path is delayed lift-off plus a glide path -/

/-- Galí (2015), eqs. (48)–(49), p. 151; Cochrane (2023), §20.2.4, p. 479: on the announced
zero-rate spell `[0, t_C]` the commitment path obeys the zero-rate recursion with forcing
`−rⁿ_t` (the same recursion as the delayed-lift-off family). -/
theorem comm_step {β κ σ ρ η : ℝ} {tZ tC : ℕ} {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (t : ℕ) (ht : t < tC + 1) :
    (x t, π t) = backStep β κ σ (-natRate ρ η tZ t) (x (t + 1), π (t + 1)) := by
  rcases le_or_gt t tZ with h | h
  · rw [natRate_of_le h, neg_neg]; exact h48 t h
  · rw [natRate_of_lt h]; exact h49 t h (by omega)

/-- Galí (2015), eqs. (36), (29), (43), pp. 149–150; Cochrane (2023), §20.2.4, p. 479 (the
promise at lift-off): at the lift-off date `t_C + 1` of Galí's algorithm, with `ξ₂,t_C ≥ 0`,
`ξ₂,t_C+1 = 0` and `ξ₁,t_C+1 > 0`, both output and inflation are strictly positive. -/
theorem comm_liftoff_pos {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ} (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1))
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0) (hsign : 0 ≤ ξ2 tC)
    (hξ : 0 < ξ1 (tC + 1)) : 0 < x (tC + 1) ∧ 0 < π (tC + 1) := by
  have hl : lag ξ2 (tC + 1) = ξ2 tC := rfl
  unfold FOC36 at h36
  rw [hl, hξ2] at h36
  have h1 : ϑ * x (tC + 1) = κ * ξ1 (tC + 1) + ξ2 tC / β := by linarith
  have h2 : 0 < κ * ξ1 (tC + 1) + ξ2 tC / β :=
    add_pos_of_pos_of_nonneg (mul_pos hκ hξ) (div_nonneg hsign hβ.le)
  have hx : 0 < x (tC + 1) := (mul_pos_iff_of_pos_left hϑ).mp (h1 ▸ h2)
  refine ⟨hx, ?_⟩
  unfold NKPC at h46
  have hp := post_eq43_pos hβ hβ1 hκ hϑ hξ 0
  rw [← hπ2] at hp
  rw [h46]
  have h3 : 0 < β * π (tC + 1 + 1) := mul_pos hβ hp
  exact add_pos h3 (mul_pos hκ hx)

/-- Cochrane (2023), §20.2.4, p. 479 (forward guidance = delayed lift-off **plus** a promise),
for Galí's (2015) optimal commitment path, pp. 149–152: on `[0, t_C + 1]` the commitment path
lies strictly above the delayed-lift-off path with the same lift-off date `t_C + 1` (both
components). Both obey the same zero-rate recursion; they differ only in the promise at lift-off,
`(x, π)_{t_C+1} > 0` (`comm_liftoff_pos`) against `0`. -/
theorem comm_gt_delay {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) {tZ tC : ℕ} {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0) (hsign : 0 ≤ ξ2 tC)
    (hξ : 0 < ξ1 (tC + 1)) (t : ℕ) (ht : t ≤ tC + 1) :
    (delayPath β κ σ ρ η tZ (tC + 1) t).1 < x t ∧ (delayPath β κ σ ρ η tZ (tC + 1) t).2 < π t := by
  obtain ⟨hx, hp⟩ := comm_liftoff_pos hβ hβ1 hκ hϑ h36 h46 hξ2 hπ2 hsign hξ
  have hd : delayPath β κ σ ρ η tZ (tC + 1) (tC + 1) = (0, 0) := delay_after le_rfl
  rcases Nat.lt_or_ge t (tC + 1) with h | h
  · exact zr_strict hβ.le hκ hσ (e := fun t => -natRate ρ η tZ t) (N := tC + 1)
      (p := fun t => (x t, π t)) (fun s hs => comm_step h48 h49 s hs)
      (fun s hs => delay_step hs) (by rw [hd]; exact hx.le) (by rw [hd]; exact hp.le)
      (by rw [hd]; exact Or.inl hx) t h
  · obtain rfl : t = tC + 1 := by omega
    rw [hd]
    exact ⟨hx, hp⟩

/-- Cochrane (2023), §20.2.4, pp. 478–479, and Galí (2015), §5.4.2, pp. 148–152: **the optimal
commitment path raises output and inflation at every date relative to discretion**. Assume the
form of the path delivered by Galí's algorithm (`ZLBCommitment.algorithm_verification`):
(48)–(49) on the zero-rate spell `[0, t_C]` with `t_C ≥ t_Z`, the FOC (36) and the Phillips curve at
`t_C + 1`, `ξ₂,t_C ≥ 0 = ξ₂,t_C+1`, `ξ₁,t_C+1 > 0`, and the closed form (42)–(43) after lift-off,
we get `discX_t < x_t` and `discPi_t < π_t` for every `t`. -/
theorem comm_gt_disc {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) (t : ℕ) :
    discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t := by
  have hπ2 : π (tC + 2) = postPi β κ ϑ (ξ1 (tC + 1)) 0 := by simpa using (hpost 0).2
  rcases Nat.lt_or_ge t (tC + 2) with h | h
  · have a := comm_gt_delay hβ hβ1 hκ hσ hϑ (ρ := ρ) (η := η) (tZ := tZ) h48 h49 h36 h46 hξ2
      hπ2 hsign hξ t (by omega)
    have b := delay_le_of_le (η := η) hβ.le hκ hσ hρ (tZ := tZ) le_rfl
      (show tZ + 1 ≤ tC + 1 by omega) t
    rw [delay_eq_disc] at b
    exact ⟨b.1.trans_lt a.1, b.2.trans_lt a.2⟩
  · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
    have hz := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ)))
      (show tZ < tC + k + 2 by omega)
    unfold discX discPi
    rw [hz, (hpost k).1, (hpost k).2]
    exact ⟨post_eq42_pos hβ hκ hϑ hξ k, post_eq43_pos hβ hβ1 hκ hϑ hξ k⟩

/-- Cochrane (2023), §20.2.4, p. 479 ("commits to delaying an interest-rate rise"), Galí (2015),
pp. 151–152: the commitment path keeps `i = 0` on `[0, t_C]`; on `(t_Z, t_C]` this is strictly
below the natural rate `ρ` (the delayed lift-off), whereas the discretionary rate equals the
natural rate `ρ` at every date after `t_Z`. -/
theorem comm_rates {β κ σ ρ η : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) {tZ tC : ℕ} {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1))) :
    (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, tZ < t → t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t < natRate ρ η tZ t) ∧
      ∀ t, tZ < t →
        impliedRate σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) t = ρ := by
  have h0 : ∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0 := by
    intro t ht
    have := (backStep_rate (rn := natRate ρ η tZ) hσ.ne' (comm_step h48 h49 t (by omega))).2
    rw [this]; ring
  refine ⟨h0, fun t h1 h2 => ?_, fun t ht => ?_⟩
  · rw [h0 t h2, natRate_of_lt h1]; exact hρ
  · have a := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ))) ht
    have b := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ)))
      (show tZ < t + 1 by omega)
    simp only [impliedRate, discX, discPi, a, b, natRate_of_lt ht]
    ring

/-- Galí (2015), p. 149 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 485: a
nonnegative summable sequence with nonpositive sum vanishes. -/
theorem eq_zero_of_tsum_nonpos {D : ℕ → ℝ} (h0 : ∀ t, 0 ≤ D t) (hs : Summable D)
    (h : ∑' t, D t ≤ 0) (t : ℕ) : D t = 0 :=
  le_antisymm ((hs.le_tsum t fun j _ => h0 j).trans h) (h0 t)

/-- Galí (2015), p. 149 (restated from the Galí Chapter 5 project); Cochrane (2023), p. 485:
`β^t (a² + ϑ b²) = 0` forces `a = b = 0`. -/
theorem sq_terms_zero {β ϑ a b : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (t : ℕ)
    (h : β ^ t * (a ^ 2 + ϑ * b ^ 2) = 0) : a = 0 ∧ b = 0 := by
  have hp : 0 < β ^ t := pow_pos hβ t
  have h2 : a ^ 2 + ϑ * b ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hp.ne'
    · exact h'
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hϑ.le (sq_nonneg b)]
  have hb : ϑ * b ^ 2 = 0 := by linarith
  exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha,
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      ((mul_eq_zero.mp hb).resolve_left hϑ.ne')⟩

/-- Galí (2015), p. 149, restated from the Galí Chapter 5 project
(`ZLBCommitment.optimal_unique`); Cochrane (2023), §20.2.4, p. 479: strict convexity — two
optimal paths of the commitment problem coincide. -/
theorem optimal_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) {rn x1 π1 x2 π2 : ℕ → ℝ}
    (h1 : Optimal β κ σ ϑ rn x1 π1) (h2 : Optimal β κ σ ϑ rn x2 π2) : x1 = x2 ∧ π1 = π2 := by
  obtain ⟨hF1, hs1, ho1⟩ := h1
  obtain ⟨hF2, hs2, ho2⟩ := h2
  set xm : ℕ → ℝ := fun t => (x1 t + x2 t) / 2 with hxm
  set πm : ℕ → ℝ := fun t => (π1 t + π2 t) / 2 with hπm
  have hFm : Feasible β κ σ rn xm πm := by
    intro t
    obtain ⟨a1, b1⟩ := hF1 t
    obtain ⟨a2, b2⟩ := hF2 t
    unfold NKPC at a1 a2
    refine ⟨?_, ?_⟩
    · unfold NKPC; simp only [hxm, hπm]; linarith
    · have e : ups1 σ rn xm πm t = (ups1 σ rn x1 π1 t + ups1 σ rn x2 π2 t) / 2 := by
        simp only [ups1, hxm, hπm]; ring
      rw [e]; simp only [hxm]; linarith
  set D : ℕ → ℝ := fun t => β ^ t * ((π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hs1.add hs2).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (π1 t - π2 t) ^ 2 + ϑ * (x1 t - x2 t) ^ 2 ≤
        2 * ((π1 t ^ 2 + ϑ * x1 t ^ 2) + (π2 t ^ 2 + ϑ * x2 t ^ 2)) := by
      nlinarith [sq_nonneg (π1 t + π2 t), sq_nonneg (x1 t + x2 t)]
    nlinarith
  have hterm : ∀ t, lossTerm β ϑ xm πm t =
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 := by
    intro t; simp only [lossTerm, hDdef, hxm, hπm]; ring
  have hsm : Summable (lossTerm β ϑ xm πm) := by
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    exact ((hs1.add hs2).div_const 2).sub (hDs.div_const 4)
  have hlm : loss β ϑ xm πm = (loss β ϑ x1 π1 + loss β ϑ x2 π2) / 2 - (∑' t, D t) / 4 := by
    unfold loss
    rw [show lossTerm β ϑ xm πm = fun t =>
      (lossTerm β ϑ x1 π1 t + lossTerm β ϑ x2 π2 t) / 2 - D t / 4 from funext hterm]
    rw [((hs1.add hs2).div_const 2).tsum_sub (hDs.div_const 4), tsum_div_const,
      tsum_div_const, hs1.tsum_add hs2]
  have l12 := ho1 x2 π2 hF2 hs2
  have l21 := ho2 x1 π1 hF1 hs1
  have l1m := ho1 xm πm hFm hsm
  have hz := eq_zero_of_tsum_nonpos hD0 hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-- Galí (2015), pp. 146–147; Cochrane (2023), §20.2.4, p. 479: the discretionary path is
feasible for the commitment problem (`i ≥ 0`, with `ρ ≥ 0`) and has finite loss (it vanishes
after `t_Z`). -/
theorem disc_feasible_summable {β κ σ ϑ ρ η : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (tZ : ℕ) :
    Feasible β κ σ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) ∧
      Summable (lossTerm β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ)) := by
  have e1 : discX β κ σ η tZ = fun s => (delayPath β κ σ ρ η tZ (tZ + 1) s).1 :=
    funext fun s => by rw [delay_eq_disc]; rfl
  have e2 : discPi β κ σ η tZ = fun s => (delayPath β κ σ ρ η tZ (tZ + 1) s).2 :=
    funext fun s => by rw [delay_eq_disc]; rfl
  refine ⟨by rw [e1, e2]; exact delay_feasible hσ hρ le_rfl, ?_⟩
  refine summable_of_ne_finset_zero (s := Finset.range (tZ + 1)) fun t ht => ?_
  have h : tZ < t := by simp only [Finset.mem_range, not_lt] at ht; omega
  have hz := zlbPath_of_lt (β := β) (κ := κ) (σ := σ) (η := η) (sT := ((0 : ℝ), (0 : ℝ))) h
  simp only [lossTerm, discX, discPi, hz]
  ring

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), §5.4.2, p. 152: **discretion is strictly
worse than commitment**. If the commitment path of `comm_gt_disc` is the commitment optimum (as
`ZLBCommitment.algorithm_verification` proves when its sign conditions hold), the discretionary
path, feasible with finite loss, has strictly larger loss. -/
theorem comm_loss_lt {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1))
    (hopt : Optimal β κ σ ϑ (natRate ρ η tZ) x π) :
    loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) := by
  obtain ⟨hdF, hdS⟩ := disc_feasible_summable (ϑ := ϑ) (η := η) hσ hρ.le tZ
  have hle := hopt.2.2 _ _ hdF hdS
  by_contra hnot
  push Not at hnot
  have hdopt : Optimal β κ σ ϑ (natRate ρ η tZ) (discX β κ σ η tZ) (discPi β κ σ η tZ) :=
    ⟨hdF, hdS, fun y q hy hs => hnot.trans (hopt.2.2 y q hy hs)⟩
  have heq := optimal_unique hβ hϑ hopt hdopt
  have h0 := comm_gt_disc hβ hβ1 hκ hσ hϑ hρ htC h48 h49 h36 h46 hξ2 hpost hsign hξ 0
  rw [heq.1] at h0
  exact lt_irrefl _ h0.1

/-! ## The discrete Werning family: forward guidance about `π_T` -/

/-- Cochrane (2023), eq. (5.6), p. 119 and §20.1, p. 467: the unstable root `λ₁` of the peg
(`ZLBPeg.lam1`) for Galí's model, whose IS slope `σ⁻¹` is Cochrane's `σ`. -/
noncomputable def l1 (β σ κ : ℝ) : ℝ := ZLBPeg.lam1 β σ⁻¹ κ

/-- Cochrane (2023), eq. (5.6), p. 119: the stable root `λ₂` (`ZLBPeg.lam2`) for Galí's model. -/
noncomputable def l2 (β σ κ : ℝ) : ℝ := ZLBPeg.lam2 β σ⁻¹ κ

/-- Cochrane (2023), §20.1, p. 467 (`ZLBPeg.peg_slaving`): the output gap per unit of inflation
on a bounded peg path, `x = (1 − λ₂)π/κ`. -/
noncomputable def vx (β σ κ : ℝ) : ℝ := (1 - l2 β σ κ) / κ

/-- Cochrane (2023), eq. (5.6), p. 119: `1 < λ₁` for Galí's model. -/
theorem one_lt_l1 {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) : 1 < l1 β σ κ :=
  ZLBPeg.one_lt_lam1 hβ (by positivity)

/-- Cochrane (2023), eq. (5.6), p. 119 and p. 475 (the bounded peg path is an eigenvector of the
backward map): `λ₁ v_x = v_x + σ⁻¹`. -/
theorem l1_vx {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    l1 β σ κ * vx β σ κ = vx β σ κ + σ⁻¹ := by
  have ha := ZLBPeg.lam_add β σ⁻¹ κ
  have hm := ZLBPeg.lam_mul hβ (show 0 < σ⁻¹ * κ by positivity)
  have key : (l1 β σ κ - 1) * (1 - l2 β σ κ) = σ⁻¹ * κ := by
    unfold l1 l2
    linear_combination ha - hm
  have e : l1 β σ κ * vx β σ κ - vx β σ κ = (l1 β σ κ - 1) * (1 - l2 β σ κ) / κ := by
    unfold vx; ring
  rw [key, mul_div_assoc, div_self hκ.ne', mul_one] at e
  linarith

/-- Cochrane (2023), eq. (5.6), p. 119: `κ v_x + β + κ/σ = λ₁`. -/
theorem kappa_vx {β σ κ : ℝ} (hκ : 0 < κ) : κ * vx β σ κ + (β + κ / σ) = l1 β σ κ := by
  have ha : l1 β σ κ + l2 β σ κ = 1 + β + σ⁻¹ * κ := ZLBPeg.lam_add β σ⁻¹ κ
  have hv : κ * vx β σ κ = 1 - l2 β σ κ := by
    unfold vx; field_simp
  rw [hv, div_eq_mul_inv]
  linarith

/-- Cochrane (2023), §20.1, p. 467 and §20.2.2, p. 475: at a rate equal to the natural rate
(`e = 0`) the backward map multiplies the peg direction `(v_x, 1)` by `λ₁`. -/
theorem backStep_eigen {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (a : ℝ) :
    backStep β κ σ 0 (a * vx β σ κ, a) = (l1 β σ κ * (a * vx β σ κ), l1 β σ κ * a) := by
  have h1 := l1_vx hβ hσ hκ
  have h2 := kappa_vx (β := β) (σ := σ) hκ
  simp only [backStep]
  ext
  · simp only
    linear_combination (-a) * h1
  · simp only
    linear_combination a * h2

/-- Cochrane (2023), §20.2.2, p. 475 (the Werning family), in Galí's discrete model: rate `0`
during the trap `[0, t_Z]`, rate equal to the natural rate afterwards, and the bounded peg
continuation `π_{t_Z+1+k} = λ₁⁻ᵏ c`, `x = v_x π` after the trap; `c = π_{t_Z+1}` plays the role
of Werning's `π_T`. -/
noncomputable def wState (β κ σ η : ℝ) (tZ : ℕ) (c : ℝ) (t : ℕ) : ℝ × ℝ :=
  if t ≤ tZ then backState β κ σ η (c * vx β σ κ, c) (tZ + 1 - t)
  else ((l1 β σ κ)⁻¹ ^ (t - (tZ + 1)) * (c * vx β σ κ), (l1 β σ κ)⁻¹ ^ (t - (tZ + 1)) * c)

/-- Cochrane (2023), p. 475: after the trap the family member is on the peg path. -/
theorem w_post {β κ σ η : ℝ} {tZ : ℕ} (c : ℝ) (k : ℕ) :
    wState β κ σ η tZ c (tZ + 1 + k) =
      ((l1 β σ κ)⁻¹ ^ k * (c * vx β σ κ), (l1 β σ κ)⁻¹ ^ k * c) := by
  simp only [wState, show ¬ tZ + 1 + k ≤ tZ by omega, ↓reduceIte,
    show tZ + 1 + k - (tZ + 1) = k by omega]

/-- Cochrane (2023), p. 475: at the end of the trap the member is at `(c v_x, c)`. -/
theorem w_end {β κ σ η : ℝ} {tZ : ℕ} (c : ℝ) :
    wState β κ σ η tZ c (tZ + 1) = (c * vx β σ κ, c) := by
  have := w_post (β := β) (κ := κ) (σ := σ) (η := η) (tZ := tZ) c 0
  simpa using this

/-- Galí (2015), eq. (34), p. 147; Cochrane (2023), p. 475: during the trap the member obeys the
binding-bound recursion (34). -/
theorem w_trap {β κ σ η : ℝ} {tZ t : ℕ} (c : ℝ) (ht : t ≤ tZ) :
    wState β κ σ η tZ c t = backStep β κ σ η (wState β κ σ η tZ c (t + 1)) := by
  by_cases h : t + 1 ≤ tZ
  · simp only [wState, ht, h, ↓reduceIte, show tZ + 1 - t = (tZ + 1 - (t + 1)) + 1 by omega,
      backState]
  · have htz : tZ = t := by omega
    subst htz
    rw [w_end]
    simp only [wState, le_rfl, ↓reduceIte, show tZ + 1 - tZ = 0 + 1 by omega, backState]

/-- Cochrane (2023), §20.1, p. 467: after the trap the member obeys the peg recursion
`(x_t, π_t) = A(x_{t+1}, π_{t+1})` (rate equal to the natural rate). -/
theorem w_after {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ t : ℕ} (c : ℝ)
    (ht : tZ < t) :
    wState β κ σ η tZ c t = backStep β κ σ 0 (wState β κ σ η tZ c (t + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = tZ + 1 + k := ⟨t - (tZ + 1), by omega⟩
  rw [show tZ + 1 + k + 1 = tZ + 1 + (k + 1) by omega, w_post, w_post,
    show (l1 β σ κ)⁻¹ ^ (k + 1) * (c * vx β σ κ) = ((l1 β σ κ)⁻¹ ^ (k + 1) * c) * vx β σ κ by
      ring, backStep_eigen hβ hσ hκ]
  have hl : l1 β σ κ ≠ 0 := by linarith [one_lt_l1 hβ hσ hκ]
  have e : l1 β σ κ * ((l1 β σ κ)⁻¹ ^ (k + 1) * c) = (l1 β σ κ)⁻¹ ^ k * c := by
    rw [pow_succ]; field_simp
  have e2 : l1 β σ κ * ((l1 β σ κ)⁻¹ ^ (k + 1) * c * vx β σ κ) =
      (l1 β σ κ)⁻¹ ^ k * c * vx β σ κ := by rw [← mul_assoc, e]
  rw [e, e2]
  ext
  · simp only; ring
  · simp only

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.wPath_isPath`, discrete): every member
satisfies the Phillips curve at every date, has `i = 0` during the trap and `i = rⁿ` after. -/
theorem w_isPath {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ : ℕ} (c : ℝ) :
    (∀ t, NKPC β κ (fun s => (wState β κ σ η tZ c s).1) (fun s => (wState β κ σ η tZ c s).2) t) ∧
      (∀ t, t ≤ tZ → impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = 0) ∧
      (∀ t, tZ < t → impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = natRate ρ η tZ t) := by
  have hA : ∀ t, t ≤ tZ → NKPC β κ (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = 0 := by
    intro t ht
    have h := backStep_rate (rn := natRate ρ η tZ) (x := fun s => (wState β κ σ η tZ c s).1)
      (π := fun s => (wState β κ σ η tZ c s).2) (t := t) hσ.ne' (w_trap c ht)
    exact ⟨h.1, by rw [h.2, natRate_of_le ht]; ring⟩
  have hB : ∀ t, tZ < t → NKPC β κ (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t ∧
      impliedRate σ (natRate ρ η tZ) (fun s => (wState β κ σ η tZ c s).1)
        (fun s => (wState β κ σ η tZ c s).2) t = natRate ρ η tZ t := by
    intro t ht
    have h := backStep_rate (rn := natRate ρ η tZ) (x := fun s => (wState β κ σ η tZ c s).1)
      (π := fun s => (wState β κ σ η tZ c s).2) (t := t) hσ.ne' (w_after hβ hσ hκ c ht)
    exact ⟨h.1, by rw [h.2, add_zero]⟩
  refine ⟨fun t => ?_, fun t ht => (hA t ht).2, fun t ht => (hB t ht).2⟩
  rcases le_or_gt t tZ with h | h
  · exact (hA t h).1
  · exact (hB t h).1

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.wPath_bdd`, discrete): every member is
bounded. -/
theorem w_bdd {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (tZ : ℕ) (c : ℝ) :
    ∃ M, ∀ t, |(wState β κ σ η tZ c t).1| ≤ M ∧ |(wState β κ σ η tZ c t).2| ≤ M := by
  set S := ∑ s ∈ Finset.range (tZ + 1),
    (|(wState β κ σ η tZ c s).1| + |(wState β κ σ η tZ c s).2|) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hl := one_lt_l1 hβ hσ hκ
  have hi0 : 0 ≤ (l1 β σ κ)⁻¹ := inv_nonneg.2 (by linarith)
  have hi1 : (l1 β σ κ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hl.le
  refine ⟨S + |c * vx β σ κ| + |c|, fun t => ?_⟩
  have a1 := abs_nonneg (c * vx β σ κ)
  have a2 := abs_nonneg c
  rcases le_or_gt t tZ with h | h
  · have hle := Finset.single_le_sum
      (f := fun s => |(wState β κ σ η tZ c s).1| + |(wState β κ σ η tZ c s).2|)
      (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
    have b1 := abs_nonneg (wState β κ σ η tZ c t).1
    have b2 := abs_nonneg (wState β κ σ η tZ c t).2
    constructor <;> linarith
  · obtain ⟨k, rfl⟩ : ∃ k, t = tZ + 1 + k := ⟨t - (tZ + 1), by omega⟩
    rw [w_post]
    have hp0 : 0 ≤ (l1 β σ κ)⁻¹ ^ k := pow_nonneg hi0 k
    have hp1 : (l1 β σ κ)⁻¹ ^ k ≤ 1 := pow_le_one₀ hi0 hi1
    simp only [abs_mul, abs_of_nonneg hp0]
    have e1 : (l1 β σ κ)⁻¹ ^ k * (|c| * |vx β σ κ|) ≤ |c| * |vx β σ κ| :=
      mul_le_of_le_one_left (by positivity) hp1
    have e2 : (l1 β σ κ)⁻¹ ^ k * |c| ≤ |c| := mul_le_of_le_one_left a2 hp1
    rw [abs_mul] at a1
    constructor <;> nlinarith

/-- Cochrane (2023), §20.2.2, p. 475 (the new-Keynesian selection `π_T = 0`) and Galí (2015),
p. 147: the member with `c = 0` is Galí's discretionary path. -/
theorem w_zero (β κ σ η : ℝ) (tZ t : ℕ) :
    wState β κ σ η tZ 0 t = zlbPath β κ σ η tZ (0, 0) t := by
  by_cases h : t ≤ tZ
  · simp only [wState, zlbPath, h, ↓reduceIte, zero_mul]
  · simp only [wState, zlbPath, h, ↓reduceIte, zero_mul, mul_zero]

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.dpi_dpiT`, discrete): across the family,
`π_t(c) − π_t(c') = λ₁^{t_Z+1−t}(c − c')` and `x_t(c) − x_t(c') = λ₁^{t_Z+1−t}(c − c')v_x` at
every date of the trap and at its end. -/
theorem w_sub {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ t : ℕ} (c c' : ℝ)
    (ht : t ≤ tZ + 1) :
    (wState β κ σ η tZ c t).1 - (wState β κ σ η tZ c' t).1 =
        l1 β σ κ ^ (tZ + 1 - t) * ((c - c') * vx β σ κ) ∧
      (wState β κ σ η tZ c t).2 - (wState β κ σ η tZ c' t).2 =
        l1 β σ κ ^ (tZ + 1 - t) * (c - c') := by
  have h1 := l1_vx hβ hσ hκ
  have h2 := kappa_vx (β := β) (σ := σ) hκ
  refine down_ind (N := tZ + 1) (P := fun t => (wState β κ σ η tZ c t).1 -
      (wState β κ σ η tZ c' t).1 = l1 β σ κ ^ (tZ + 1 - t) * ((c - c') * vx β σ κ) ∧
      (wState β κ σ η tZ c t).2 - (wState β κ σ η tZ c' t).2 =
        l1 β σ κ ^ (tZ + 1 - t) * (c - c')) ?_ (fun s hs ih => ?_) t ht
  · rw [w_end, w_end]
    exact ⟨by simp only [Nat.sub_self, pow_zero, one_mul]; ring,
      by simp only [Nat.sub_self, pow_zero, one_mul]⟩
  · have e := backStep_sub_fst β κ σ η (wState β κ σ η tZ c (s + 1))
      (wState β κ σ η tZ c' (s + 1))
    have f := backStep_sub_snd β κ σ η (wState β κ σ η tZ c (s + 1))
      (wState β κ σ η tZ c' (s + 1))
    rw [← w_trap c (by omega), ← w_trap c' (by omega), ih.1, ih.2] at e f
    rw [e, f, show tZ + 1 - s = (tZ + 1 - (s + 1)) + 1 by omega, pow_succ]
    constructor
    · linear_combination (-(l1 β σ κ ^ (tZ + 1 - (s + 1)) * (c - c'))) * h1
    · linear_combination l1 β σ κ ^ (tZ + 1 - (s + 1)) * (c - c') * h2

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.dpi0_dpiT`, discrete): **date-0
inflation moves one-for-`λ₁^{t_Z+1}` with the promise `c`**: `π₀(c) − π₀(c') =
λ₁^{t_Z+1}(c − c')`, and `π₀(c) = π₀^{disc} + λ₁^{t_Z+1} c`. -/
theorem w_pi0_sub {β κ σ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (tZ : ℕ) (c c' : ℝ) :
    (wState β κ σ η tZ c 0).2 - (wState β κ σ η tZ c' 0).2 = l1 β σ κ ^ (tZ + 1) * (c - c') ∧
      (wState β κ σ η tZ c 0).2 = discPi β κ σ η tZ 0 + l1 β σ κ ^ (tZ + 1) * c := by
  have h := (w_sub (η := η) hβ hσ hκ (tZ := tZ) (t := 0) c c' (by omega)).2
  have h0 := (w_sub (η := η) hβ hσ hκ (tZ := tZ) (t := 0) c 0 (by omega)).2
  rw [Nat.sub_zero] at h h0
  refine ⟨h, ?_⟩
  rw [w_zero] at h0
  unfold discPi
  linarith

/-- Cochrane (2023), §20.2.4, p. 479 ("promises about actions further in the future have greater
effects today", `ForwardGuidance.sensitivity_strictMono_T`, discrete): the sensitivity `λ₁ⁿ` is
strictly increasing in the length `n` of the trap. -/
theorem w_sensitivity_strictMono {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    StrictMono fun n : ℕ => l1 β σ κ ^ n :=
  pow_right_strictMono₀ (one_lt_l1 hβ hσ hκ)

/-- Cochrane (2023), §20.2.4, p. 479 (`ForwardGuidance.sensitivity_tendsto_T`, discrete): the
sensitivity is unbounded in the length of the trap. -/
theorem w_sensitivity_tendsto {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => l1 β σ κ ^ n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (one_lt_l1 hβ hσ hκ)

/-- Cochrane (2023), §5.7.1, p. 165 and §20.2.4, p. 479 (**the discrete sensitivity converges to
Werning's `e^{λ^b T}`**, `ForwardGuidance.dpi0_dpiT`): with period length `t/n` (`β = 1 − ρt/n`,
Galí's IS slope `σ⁻¹ = σt/n`, `κt/n`), the sensitivity `λ₁ⁿ` of `π₀` to the promise after `n`
periods tends to `e^{λ^b t}` (via `Links.tendsto_peg_decay`). -/
theorem sensitivity_tendsto_exp {ρ σ κ t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => l1 (1 - ρ * (t / n)) (σ * (t / n))⁻¹ (κ * (t / n)) ^ n) atTop
      (𝓝 (Real.exp (ContinuousTimeNK.lamb ρ κ σ * t))) := by
  have h := (Links.tendsto_peg_decay (ρ := ρ) (mul_pos hσ hκ) ht).inv₀ (Real.exp_pos _).ne'
  rw [Real.exp_neg, inv_inv] at h
  refine h.congr fun n => ?_
  simp only [l1, inv_inv, inv_pow]

/-- Cochrane (2023), §20.2.2, p. 475 (`WerningModel.bdd_path_iff`, discrete): **every** bounded
path with the Phillips curve, `i = 0` during the trap and `i = rⁿ` after it is the member
`c = π_{t_Z+1}` of the family (the post-trap peg pins `x = v_x π` and `π_{t+1} = λ₁⁻¹π_t` by
`ZLBPeg.peg_slaving` and `Links.peg_pf_path`; the trap is pinned backward). -/
theorem w_unique {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ : ℕ}
    {x π : ℕ → ℝ} (hb : ∃ M, ∀ t, |x t| ≤ M ∧ |π t| ≤ M) (hN : ∀ t, NKPC β κ x π t)
    (h0 : ∀ t, t ≤ tZ → impliedRate σ (natRate ρ η tZ) x π t = 0)
    (h1 : ∀ t, tZ < t → impliedRate σ (natRate ρ η tZ) x π t = natRate ρ η tZ t) (t : ℕ) :
    (x t, π t) = wState β κ σ η tZ (π (tZ + 1)) t := by
  obtain ⟨M, hM⟩ := hb
  have hσκ : 0 < σ⁻¹ * κ := by positivity
  set X : ℕ → Unit → ℝ := fun k _ => x (tZ + 1 + k) with hX
  set P : ℕ → Unit → ℝ := fun k _ => π (tZ + 1 + k) with hP
  have hbX : BoundedProc X := ⟨M, fun k _ => (hM _).1⟩
  have hbP : BoundedProc P := ⟨M, fun k _ => (hM _).2⟩
  have hpeg : ZLBPeg.PegEq perfectForesight β σ⁻¹ κ 0 X P := by
    intro k ω
    have hr := h1 (tZ + 1 + k) (by omega)
    unfold impliedRate at hr
    rw [natRate_of_lt (by omega)] at hr
    have hn := hN (tZ + 1 + k)
    unfold NKPC at hn
    have e : tZ + 1 + (k + 1) = tZ + 1 + k + 1 := by omega
    constructor
    · change x (tZ + 1 + k) = x (tZ + 1 + (k + 1)) - σ⁻¹ * (0 - π (tZ + 1 + (k + 1)))
      rw [e]
      have h3 : σ * (x (tZ + 1 + k + 1) - x (tZ + 1 + k)) = -π (tZ + 1 + k + 1) := by linarith
      have h4 : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ.ne'
      linear_combination (-σ⁻¹) * h3 + (x (tZ + 1 + k + 1) - x (tZ + 1 + k)) * h4
    · change π (tZ + 1 + k) = β * π (tZ + 1 + (k + 1)) + κ * x (tZ + 1 + k)
      rw [e]; exact hn
  have hpost : ∀ k, (x (tZ + 1 + k), π (tZ + 1 + k)) =
      wState β κ σ η tZ (π (tZ + 1)) (tZ + 1 + k) := by
    intro k
    have hs := ZLBPeg.peg_slaving perfectForesight hβ hσκ hbX hbP hpeg k ()
    have hp := Links.peg_pf_path hβ hσκ hbX hbP hpeg k
    simp only [hX, hP, add_zero, sub_zero, mul_zero] at hs hp
    rw [w_post]
    have hπk : π (tZ + 1 + k) = (l1 β σ κ)⁻¹ ^ k * π (tZ + 1) := hp
    have hs' : κ * x (tZ + 1 + k) + (l2 β σ κ - 1) * π (tZ + 1 + k) = 0 := hs
    have hv : κ * vx β σ κ = 1 - l2 β σ κ := by unfold vx; field_simp
    have hxk : x (tZ + 1 + k) = π (tZ + 1 + k) * vx β σ κ := by
      apply mul_left_cancel₀ hκ.ne'
      linear_combination hs' - π (tZ + 1 + k) * hv
    rw [hxk, hπk]
    ext
    · simp only; ring
    · simp only
  rcases Nat.lt_or_ge tZ t with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, t = tZ + 1 + k := ⟨t - (tZ + 1), by omega⟩
    exact hpost k
  · refine zr_eq (e := fun _ => η) (N := tZ + 1) (p := fun t => (x t, π t))
      (fun s hs => backStep_of_rate (rn := natRate ρ η tZ) hσ.ne' (hN s) ?_)
      (fun s hs => w_trap (tZ := tZ) (t := s) _ (by omega)) ?_ t (by omega)
    · rw [h0 s (by omega), natRate_of_le (by omega)]; ring
    · simpa using hpost 0

/-- Cochrane (2023), §20.2.2, p. 475: the discrete Werning family is exactly the set of bounded
paths with the Phillips curve, `i = 0` in the trap and `i = rⁿ` after it, and the index is
`c = π_{t_Z+1}` (existence, uniqueness and characterisation). -/
theorem w_family_iff {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) {tZ : ℕ}
    {x π : ℕ → ℝ} :
    ((∃ M, ∀ t, |x t| ≤ M ∧ |π t| ≤ M) ∧ (∀ t, NKPC β κ x π t) ∧
      (∀ t, t ≤ tZ → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, tZ < t → impliedRate σ (natRate ρ η tZ) x π t = natRate ρ η tZ t)) ↔
      ∃ c, ∀ t, (x t, π t) = wState β κ σ η tZ c t := by
  constructor
  · rintro ⟨hb, hN, h0, h1⟩
    exact ⟨π (tZ + 1), w_unique hβ hσ hκ hb hN h0 h1⟩
  · rintro ⟨c, hc⟩
    have hx : x = fun s => (wState β κ σ η tZ c s).1 := funext fun s => by rw [← hc s]
    have hπ : π = fun s => (wState β κ σ η tZ c s).2 := funext fun s => by rw [← hc s]
    obtain ⟨M, hM⟩ := w_bdd (η := η) hβ hσ hκ tZ c
    obtain ⟨a, b, d⟩ := w_isPath (ρ := ρ) (η := η) hβ hσ hκ (tZ := tZ) c
    rw [hx, hπ]
    exact ⟨⟨M, hM⟩, a, b, d⟩

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), §5.4.2: **the commitment path is
equivalent, for date-0 inflation, to exactly one forward-guidance promise about `π_T`, and that
promise is strictly positive** (a glide path `c > 0`, `ForwardGuidance.glide_path`). -/
theorem comm_promise {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h36 : FOC36 β κ ϑ x ξ1 ξ2 (tC + 1)) (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k)
    (hsign : 0 ≤ ξ2 tC) (hξ : 0 < ξ1 (tC + 1)) :
    (∃! c, (wState β κ σ η tZ c 0).2 = π 0) ∧
      ∀ c, (wState β κ σ η tZ c 0).2 = π 0 → 0 < c := by
  have hl := one_lt_l1 hβ hσ hκ
  have hp : 0 < l1 β σ κ ^ (tZ + 1) := pow_pos (by linarith) _
  have hg := (comm_gt_disc hβ hβ1 hκ hσ hϑ hρ htC h48 h49 h36 h46 hξ2 hpost hsign hξ 0).2
  have hw : ∀ c, (wState β κ σ η tZ c 0).2 = discPi β κ σ η tZ 0 + l1 β σ κ ^ (tZ + 1) * c :=
    fun c => (w_pi0_sub (η := η) hβ hσ hκ tZ c 0).2
  refine ⟨⟨(π 0 - discPi β κ σ η tZ 0) / l1 β σ κ ^ (tZ + 1), ?_, fun c hc => ?_⟩,
    fun c hc => ?_⟩
  · beta_reduce
    rw [hw]; field_simp; ring
  · beta_reduce at hc
    rw [hw] at hc
    field_simp
    linarith
  · rw [hw] at hc
    have : 0 < l1 β σ κ ^ (tZ + 1) * c := by linarith
    exact (mul_pos_iff_of_pos_left hp).mp this

/-- Cochrane (2023), §20.2.4, p. 479: when Galí's commitment keeps the rate at zero after the
shock ends (`t_C > t_Z`) its path is **not** a member of the Werning family (whose rate
returns to the natural rate at `t_Z + 1`): commitment is delayed lift-off, not only a promise
about `π_T`. -/
theorem comm_not_member {β κ σ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ < tC) {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (c : ℝ) : ¬ ∀ t, (x t, π t) = wState β κ σ η tZ c t := by
  intro h
  have hx : x = fun s => (wState β κ σ η tZ c s).1 := funext fun s => by rw [← h s]
  have hπ : π = fun s => (wState β κ σ η tZ c s).2 := funext fun s => by rw [← h s]
  have a := (comm_rates (β := β) (κ := κ) hσ hρ h48 h49).1 (tZ + 1) (by omega)
  have b := (w_isPath (ρ := ρ) (η := η) hβ hσ hκ (tZ := tZ) c).2.2 (tZ + 1) (by omega)
  rw [← hx, ← hπ, natRate_of_lt (by omega)] at b
  linarith

/-! ## Woodford's moment constraint versus Cochrane's pathwise bound -/

namespace Moments

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (4.18)–(4.20), p. 428, restated from the Woodford Chapter 6 project
(`ZLB.dAvg`); Cochrane (2023), §20.1, p. 465: the discounted average
`Ê[f] = (1 − β) ∑ βᵗ E₀ f_t`, evaluated in the date-0 state `ω₀`. -/
noncomputable def dAvg (β : ℝ) (f : ℕ → Ω → ℝ) (ω0 : Ω) : ℝ :=
  (1 - β) * ∑' t, β ^ t * 𝔼.E 0 (f t) ω0

/-- Woodford (2003), (2.21), p. 400 (restated from the Woodford Chapter 6 project's
`Sequences.hasSum_dsum`); Cochrane (2023), p. 465: the discounted expected sum of a bounded
process converges. -/
theorem summable_disc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → Ω → ℝ}
    (hf : BoundedProc f) (ω0 : Ω) : Summable fun t => β ^ t * 𝔼.E 0 (f t) ω0 := by
  obtain ⟨M, hM⟩ := hf
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left M)
    fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  have h := 𝔼.abs_E_le (fun ω => hM t ω) 0 ω0
  have := pow_nonneg hβ0 t
  nlinarith

/-- Woodford (2003), (4.18)–(4.20) (restated from the Woodford Chapter 6 project's
`ZLB.dAvg_lincomb`); Cochrane (2023), p. 465: `Ê[a f + b g + c] = a Ê[f] + b Ê[g] + c`. -/
theorem dAvg_lincomb {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → Ω → ℝ}
    (hf : BoundedProc f) (hg : BoundedProc g) (a b c : ℝ) (ω0 : Ω) :
    dAvg 𝔼 β (fun t ω => a * f t ω + b * g t ω + c) ω0 =
      a * dAvg 𝔼 β f ω0 + b * dAvg 𝔼 β g ω0 + c := by
  have hE : ∀ t, 𝔼.E 0 (fun ω => a * f t ω + b * g t ω + c) ω0 =
      a * 𝔼.E 0 (f t) ω0 + b * 𝔼.E 0 (g t) ω0 + c := by
    intro t
    have : (fun ω => a * f t ω + b * g t ω + c) = a • f t + b • g t + (fun _ => c) := by
      funext ω; simp [smul_eq_mul]
    rw [this, map_add, map_add, map_smul, map_smul, 𝔼.const]
    rfl
  have hsf := summable_disc 𝔼 hβ0 hβ1 hf ω0
  have hsg := summable_disc 𝔼 hβ0 hβ1 hg ω0
  have hgeo : HasSum (fun t => β ^ t * c) (c / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right c
    rwa [div_eq_inv_mul]
  have htot := ((hsf.hasSum.mul_left a).add (hsg.hasSum.mul_left b)).add hgeo
  unfold dAvg
  rw [show (fun t => β ^ t * 𝔼.E 0 (fun ω => a * f t ω + b * g t ω + c) ω0) =
      fun t => a * (β ^ t * 𝔼.E 0 (f t) ω0) + b * (β ^ t * 𝔼.E 0 (g t) ω0) + β ^ t * c from
      funext fun t => by rw [hE t]; ring, htot.tsum_eq]
  have h1 : 1 - β ≠ 0 := by linarith
  field_simp

/-- Woodford (2003), (4.18) (restated from the Woodford Chapter 6 project); Cochrane (2023),
p. 465: `Ê[c] = c`. -/
theorem dAvg_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (c : ℝ) (ω0 : Ω) :
    dAvg 𝔼 β (fun _ _ => c) ω0 = c := by
  have h0 : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have := dAvg_lincomb 𝔼 hβ0 hβ1 h0 h0 0 0 c ω0
  simpa using this

/-- Woodford (2003), p. 428 (restated from the Woodford Chapter 6 project's `ZLB.dAvg_mono`);
Cochrane (2023), p. 465: `Ê` is monotone on bounded processes. -/
theorem dAvg_mono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → Ω → ℝ}
    (hf : BoundedProc f) (hg : BoundedProc g) (hfg : ∀ t ω, f t ω ≤ g t ω) (ω0 : Ω) :
    dAvg 𝔼 β f ω0 ≤ dAvg 𝔼 β g ω0 := by
  unfold dAvg
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine Summable.tsum_le_tsum (fun t => ?_) (summable_disc 𝔼 hβ0 hβ1 hf ω0)
    (summable_disc 𝔼 hβ0 hβ1 hg ω0)
  exact mul_le_mul_of_nonneg_left (𝔼.mono 0 (fun ω => hfg t ω) ω0) (pow_nonneg hβ0 t)

/-- Woodford (2003), p. 428, restated from the Woodford Chapter 6 project (`ZLB.bigK`);
Cochrane (2023), §20.1, p. 465: `K = 1 + k⁻²` (the mean at least `k` standard deviations
above zero). -/
noncomputable def bigK (k : ℝ) : ℝ := 1 + k⁻¹ ^ 2

/-- Woodford (2003), (4.18)–(4.19), p. 428, restated from the Woodford Chapter 6 project
(`ZLB.Feasible`); Cochrane (2023), §20.1, p. 465: Woodford's moment form of the bound,
`Ê[i] ≥ 0` and `Ê[i²] ≤ K (Ê[i])²`. -/
def MomentFeasible (β K : ℝ) (i : ℕ → Ω → ℝ) (ω0 : Ω) : Prop :=
  0 ≤ dAvg 𝔼 β i ω0 ∧ dAvg 𝔼 β (fun t ω => i t ω ^ 2) ω0 ≤ K * dAvg 𝔼 β i ω0 ^ 2

/-- Cochrane (2023), §20.1, p. 465 ("interest rates cannot go below zero"): the pathwise
bound `i_t ≥ 0` at every date and in every state. -/
def PathwiseZLB (i : ℕ → Ω → ℝ) : Prop := ∀ t ω, 0 ≤ i t ω

/-- Cochrane (2023), §20.1, p. 465, and Woodford (2003), (4.18), p. 428: the pathwise bound
implies the first of Woodford's two moment conditions, `Ê[i] ≥ 0`. -/
theorem pathwise_mean_nonneg {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {i : ℕ → Ω → ℝ}
    (hb : BoundedProc i) (h : PathwiseZLB i) (ω0 : Ω) : 0 ≤ dAvg 𝔼 β i ω0 := by
  have h0 : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have := dAvg_mono 𝔼 hβ0 hβ1 h0 hb h ω0
  rwa [dAvg_const 𝔼 hβ0 hβ1] at this

/-- Cochrane (2023), §20.1, p. 465, and Woodford (2003), (4.18)–(4.19), p. 428: a **pathwise
band** `a ≤ i_t ≤ b` with `0 ≤ a` and `(b − a)² ≤ 4(K − 1)a²` (`K ≥ 1`) satisfies Woodford's
moment constraint (by `Ê[(i − a)(b − i)] ≥ 0`, the Bhatia–Davis bound). -/
theorem band_moment_feasible {β K a b : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hK : 1 ≤ K)
    (ha : 0 ≤ a) (hab : (b - a) ^ 2 ≤ 4 * (K - 1) * a ^ 2) {i : ℕ → Ω → ℝ}
    (hlo : ∀ t ω, a ≤ i t ω) (hhi : ∀ t ω, i t ω ≤ b) (ω0 : Ω) :
    MomentFeasible 𝔼 β K i ω0 := by
  have hb : BoundedProc i := ⟨|a| + |b|, fun t ω => by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, le_abs_self b, abs_nonneg b, hlo t ω]
    · linarith [le_abs_self b, abs_nonneg a, hhi t ω]⟩
  have hsq : BoundedProc (fun t ω => i t ω ^ 2) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M ^ 2, fun t ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM t ω) 2⟩
  have hc : ∀ c : ℝ, BoundedProc (fun _ _ => c : ℕ → Ω → ℝ) := fun c => ⟨|c|, fun _ _ => le_rfl⟩
  set m := dAvg 𝔼 β i ω0
  set m2 := dAvg 𝔼 β (fun t ω => i t ω ^ 2) ω0
  have h1 : a ≤ m := by
    have := dAvg_mono 𝔼 hβ0 hβ1 (hc a) hb hlo ω0
    rwa [dAvg_const 𝔼 hβ0 hβ1] at this
  have h2 : m ≤ b := by
    have := dAvg_mono 𝔼 hβ0 hβ1 hb (hc b) hhi ω0
    rwa [dAvg_const 𝔼 hβ0 hβ1] at this
  have h3 : 0 ≤ -1 * m2 + (a + b) * m + -(a * b) := by
    have hq : BoundedProc (fun t ω => -1 * i t ω ^ 2 + (a + b) * i t ω + -(a * b)) := by
      obtain ⟨M1, hM1⟩ := hsq
      obtain ⟨M2, hM2⟩ := hb
      refine ⟨M1 + |a + b| * M2 + |a * b|, fun t ω => ?_⟩
      have e1 := hM1 t ω
      have e2 := hM2 t ω
      simp only at e1
      calc |-1 * i t ω ^ 2 + (a + b) * i t ω + -(a * b)|
          ≤ |-1 * i t ω ^ 2| + |(a + b) * i t ω| + |-(a * b)| := abs_add_three _ _ _
        _ = |i t ω ^ 2| + |a + b| * |i t ω| + |a * b| := by
          rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_one, one_mul]
        _ ≤ M1 + |a + b| * M2 + |a * b| := by gcongr
    have := dAvg_mono 𝔼 hβ0 hβ1 (hc 0) hq (fun t ω => by
      nlinarith [hlo t ω, hhi t ω]) ω0
    rwa [dAvg_const 𝔼 hβ0 hβ1, dAvg_lincomb 𝔼 hβ0 hβ1 hsq hb] at this
  refine ⟨ha.trans h1, ?_⟩
  nlinarith [sq_nonneg (2 * m - a - b), mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha h1 2)
    (by linarith : (0 : ℝ) ≤ K - 1)]

/-- Woodford (2003), p. 428 (the motivation: "the mean is at least `k` standard deviations above
zero" keeps violations rare), made precise as a Cantelli bound; Cochrane (2023), §20.1, p. 465.
If Woodford's constraint holds with `Ê[i] > 0` and `K ≥ 1`, the **discounted frequency of
violating the bound**, `Ê[1{i < 0}]`, is at most `(K − 1)/K` (`= 1/(1 + k²)` for `K = 1 + k⁻²`). -/
theorem violation_freq_le {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hK : 1 ≤ K)
    {i : ℕ → Ω → ℝ} (hb : BoundedProc i) {ω0 : Ω} (hF : MomentFeasible 𝔼 β K i ω0)
    (hm : 0 < dAvg 𝔼 β i ω0) :
    dAvg 𝔼 β (fun t ω => if i t ω < 0 then 1 else 0) ω0 ≤ (K - 1) / K := by
  have hsq : BoundedProc (fun t ω => i t ω ^ 2) := by
    obtain ⟨M, hM⟩ := hb
    exact ⟨M ^ 2, fun t ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM t ω) 2⟩
  set m := dAvg 𝔼 β i ω0
  set m2 := dAvg 𝔼 β (fun t ω => i t ω ^ 2) ω0
  have hK0 : 0 < K := by linarith
  set s := K * m with hs
  have hs0 : 0 < s := mul_pos hK0 hm
  have hind : BoundedProc (fun t ω => if i t ω < 0 then (1 : ℝ) else 0) :=
    ⟨1, fun t ω => by
      change |(if i t ω < 0 then (1 : ℝ) else 0)| ≤ 1
      split_ifs <;> norm_num⟩
  have hR : BoundedProc (fun t ω => 1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1) := by
    obtain ⟨M1, hM1⟩ := hsq
    obtain ⟨M2, hM2⟩ := hb
    refine ⟨|1 / s ^ 2| * M1 + |-2 / s| * M2 + 1, fun t ω => ?_⟩
    have e1 := hM1 t ω
    have e2 := hM2 t ω
    simp only at e1
    calc |1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1|
        ≤ |1 / s ^ 2 * i t ω ^ 2| + |-2 / s * i t ω| + |(1 : ℝ)| := abs_add_three _ _ _
      _ = |1 / s ^ 2| * |i t ω ^ 2| + |-2 / s| * |i t ω| + 1 := by
        rw [abs_mul, abs_mul, abs_one]
      _ ≤ |1 / s ^ 2| * M1 + |-2 / s| * M2 + 1 := by gcongr
  have hpt : ∀ t ω, (if i t ω < 0 then (1 : ℝ) else 0) ≤
      1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1 := by
    intro t ω
    have e : 1 / s ^ 2 * i t ω ^ 2 + -2 / s * i t ω + 1 = (s - i t ω) ^ 2 / s ^ 2 := by
      field_simp; ring
    rw [e]
    split_ifs with h
    · rw [le_div_iff₀ (by positivity), one_mul]
      nlinarith
    · positivity
  have hle := dAvg_mono 𝔼 hβ0 hβ1 hind hR hpt ω0
  rw [dAvg_lincomb 𝔼 hβ0 hβ1 hsq hb] at hle
  have h1 : 1 / s ^ 2 * m2 ≤ 1 / s ^ 2 * (K * m ^ 2) :=
    mul_le_mul_of_nonneg_left hF.2 (by positivity)
  have h2 : 1 / s ^ 2 * (K * m ^ 2) = 1 / K := by
    rw [hs]; field_simp
  have h3 : -2 / s * m = -2 / K := by
    rw [hs]; field_simp
  have h4 : 1 / K + -2 / K + 1 = (K - 1) / K := by field_simp; ring
  linarith

/-- Cochrane (2023), §20.1, p. 465: under the pathwise bound the discounted frequency of
violations is `0` (the indicator vanishes identically). -/
theorem pathwise_violation_freq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {i : ℕ → Ω → ℝ}
    (h : PathwiseZLB i) (ω0 : Ω) :
    dAvg 𝔼 β (fun t ω => if i t ω < 0 then 1 else 0) ω0 = 0 := by
  have e : (fun t ω => if i t ω < 0 then (1 : ℝ) else 0) = fun _ _ => 0 := by
    funext t ω
    simp [not_lt.mpr (h t ω)]
  rw [e, dAvg_const 𝔼 hβ0 hβ1]

/-- Cochrane (2023), §20.1, p. 465 (perfect foresight): `Ê` under perfect foresight is the plain
discounted average. -/
theorem dAvg_pf (β : ℝ) (f : ℕ → Unit → ℝ) :
    dAvg perfectForesight β f () = (1 - β) * ∑' t, β ^ t * f t () := rfl

/-- Cochrane (2023), §20.1, p. 465: a one-period spike `i_0 = 1`, `i_t = 0` after. -/
noncomputable def spike (t : ℕ) (_ : Unit) : ℝ := if t = 0 then 1 else 0

/-- Cochrane (2023), §20.1, p. 465: a one-period violation, `i_0 = −1`, `i_t = 9` after. -/
noncomputable def dip (t : ℕ) (_ : Unit) : ℝ := if t = 0 then -1 else 9

/-- Cochrane (2023), §20.1, p. 465: with `β = 9/10`, `Ê[spike] = Ê[spike²] = 1/10`. -/
theorem spike_moments :
    dAvg perfectForesight (9 / 10) spike () = 1 / 10 ∧
      dAvg perfectForesight (9 / 10) (fun t ω => spike t ω ^ 2) () = 1 / 10 := by
  have e1 : (fun t : ℕ => (9 / 10 : ℝ) ^ t * spike t ()) = fun t => if t = 0 then 1 else 0 := by
    funext t; unfold spike; split_ifs with h <;> simp [h]
  have e2 : (fun t : ℕ => (9 / 10 : ℝ) ^ t * spike t () ^ 2) =
      fun t => if t = 0 then 1 else 0 := by
    funext t; unfold spike; split_ifs with h <;> simp [h]
  rw [dAvg_pf, dAvg_pf, e1, e2, tsum_ite_eq]
  norm_num

/-- Cochrane (2023), §20.1, p. 465: with `β = 9/10`, `Ê[dip] = 8`, `Ê[dip²] = 73`, and the
discounted frequency of `dip < 0` is `1/10`. -/
theorem dip_moments :
    dAvg perfectForesight (9 / 10) dip () = 8 ∧
      dAvg perfectForesight (9 / 10) (fun t ω => dip t ω ^ 2) () = 73 ∧
      dAvg perfectForesight (9 / 10) (fun t ω => if dip t ω < 0 then 1 else 0) () = 1 / 10 := by
  have hg : HasSum (fun t : ℕ => (9 / 10 : ℝ) ^ t) (1 - 9 / 10)⁻¹ :=
    hasSum_geometric_of_lt_one (by norm_num) (by norm_num)
  have h1 : HasSum (fun t : ℕ => (9 / 10 : ℝ) ^ t * dip t ()) (9 * (1 - 9 / 10)⁻¹ - 10) := by
    refine ((hg.mul_left 9).sub (hasSum_ite_eq 0 (10 : ℝ))).congr_fun fun t => ?_
    unfold dip; split_ifs with h <;> simp [h] <;> ring
  have h2 : HasSum (fun t : ℕ => (9 / 10 : ℝ) ^ t * dip t () ^ 2) (81 * (1 - 9 / 10)⁻¹ - 80) := by
    refine ((hg.mul_left 81).sub (hasSum_ite_eq 0 (80 : ℝ))).congr_fun fun t => ?_
    unfold dip; split_ifs with h <;> simp [h] <;> ring
  have e3 : (fun t : ℕ => (9 / 10 : ℝ) ^ t * (if dip t () < 0 then 1 else 0)) =
      fun t => if t = 0 then 1 else 0 := by
    funext t; unfold dip; by_cases h : t = 0 <;> simp [h]
  refine ⟨?_, ?_, ?_⟩
  · rw [dAvg_pf, h1.tsum_eq]; norm_num
  · rw [dAvg_pf, h2.tsum_eq]; norm_num
  · rw [dAvg_pf, e3, tsum_ite_eq]; norm_num

/-- Cochrane (2023), §20.1, p. 465, against Woodford (2003), p. 428: **the pathwise bound does
not imply Woodford's constraint** — the spike `i_0 = 1`, `i_t = 0` is pathwise feasible but
violates `Ê[i²] ≤ K (Ê[i])²` at Woodford's `K = 1 + 2.26⁻²` (`β = 9/10`). -/
theorem pathwise_not_moment :
    BoundedProc spike ∧ PathwiseZLB spike ∧
      ¬ MomentFeasible perfectForesight (9 / 10) (bigK 2.26) spike () := by
  obtain ⟨h1, h2⟩ := spike_moments
  refine ⟨⟨1, fun t _ => by unfold spike; split_ifs <;> norm_num⟩,
    fun t _ => by unfold spike; split_ifs <;> norm_num, fun h => ?_⟩
  have := h.2
  rw [h1, h2] at this
  unfold bigK at this
  norm_num at this

/-- Woodford (2003), p. 428, against Cochrane (2023), §20.1, p. 465: **Woodford's constraint
does not imply the pathwise bound** — `i_0 = −1`, `i_t = 9` satisfies `Ê[i] = 8 ≥ 0` and
`Ê[i²] = 73 ≤ K · 64` at `K = 1 + 2.26⁻²` (`β = 9/10`) but violates `i ≥ 0` at date 0, with
discounted violation frequency `1/10 > 0` (within the Cantelli bound `violation_freq_le`). -/
theorem moment_not_pathwise :
    BoundedProc dip ∧ MomentFeasible perfectForesight (9 / 10) (bigK 2.26) dip () ∧
      ¬ PathwiseZLB dip ∧
      dAvg perfectForesight (9 / 10) (fun t ω => if dip t ω < 0 then 1 else 0) () = 1 / 10 := by
  obtain ⟨h1, h2, h3⟩ := dip_moments
  refine ⟨⟨9, fun t _ => by unfold dip; split_ifs <;> norm_num⟩, ⟨?_, ?_⟩, fun h => ?_, h3⟩
  · rw [h1]; norm_num
  · rw [h1, h2]; unfold bigK; norm_num
  · have := h 0 ()
    unfold dip at this
    norm_num at this

/-- Cochrane (2023), §20.1, p. 465, and Woodford (2003), Proposition 6.9, p. 428: **neither
treatment of the bound implies the other** (bounded rate paths, `β = 9/10`, `K = 1 + 2.26⁻²`). -/
theorem neither_implies :
    (¬ ∀ i : ℕ → Unit → ℝ, BoundedProc i → PathwiseZLB i →
        MomentFeasible perfectForesight (9 / 10) (bigK 2.26) i ()) ∧
      ¬ ∀ i : ℕ → Unit → ℝ, BoundedProc i →
        MomentFeasible perfectForesight (9 / 10) (bigK 2.26) i () → PathwiseZLB i := by
  obtain ⟨a1, a2, a3⟩ := pathwise_not_moment
  obtain ⟨b1, b2, b3, -⟩ := moment_not_pathwise
  exact ⟨fun h => a3 (h _ a1 a2), fun h => b3 (h _ b1 b2)⟩

end Moments

/-! ## The zero-bound steady state and Woodford's welfare loss -/

/-- Woodford (2003), App. E.3, p. 696, restated from the Woodford Chapter 6 project
(`Sequences.lagS`); Cochrane (2023), §20.3, p. 485: the lag `a_{t−1}` with initial value
`a_{−1}`. -/
def lagS (am1 : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => am1
  | t + 1 => a t

/-- Woodford (2003), eq. (2.20), p. 399 (Proposition 6.3), restated from the Woodford
Chapter 6 project (the hypothesis of `Sequences.disp_bdd`); Cochrane (2023), §20.3, p. 485:
the dispersion law of motion `Δ_t = αΔ_{t−1} + α/(1 − α) p_t²`. -/
def DispRec (α Δm1 : ℝ) (Δ p : ℕ → ℝ) : Prop :=
  ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2

/-- Woodford (2003), (2.20), p. 399, and Cochrane (2023), §20.3, p. 485: at constant inflation
`π`, Woodford's dispersion is `Δ_t = D + α^{t+1}(Δ_{−1} − D)`, `D = ZLBWelfare.dispersion α π`
(the shared object: Cochrane's stationary Calvo dispersion is Woodford's fixed point). -/
theorem disp_const_closed {α Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {Δ : ℕ → ℝ}
    (hrec : DispRec α Δm1 Δ fun _ => π) (t : ℕ) :
    Δ t = ZLBWelfare.dispersion α π + α ^ (t + 1) * (Δm1 - ZLBWelfare.dispersion α π) := by
  have hfix := ZLBWelfare.dispersion_fixed_point h0 h1 π
  induction t with
  | zero =>
    rw [hrec 0]
    simp only [lagS, zero_add, pow_one]
    linear_combination -hfix
  | succ t ih =>
    rw [hrec (t + 1)]
    simp only [lagS]
    rw [ih, pow_succ]
    linear_combination -hfix

/-- Woodford (2003), (2.20), and Cochrane (2023), §20.3, p. 485: at constant inflation Woodford's
dispersion converges to Cochrane's stationary dispersion `ZLBWelfare.dispersion α π`. -/
theorem disp_const_tendsto {α Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {Δ : ℕ → ℝ}
    (hrec : DispRec α Δm1 Δ fun _ => π) :
    Tendsto Δ atTop (𝓝 (ZLBWelfare.dispersion α π)) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp
    (tendsto_add_atTop_nat 1)).mul_const (Δm1 - ZLBWelfare.dispersion α π)
  rw [zero_mul] at h
  have h2 := h.const_add (ZLBWelfare.dispersion α π)
  rw [add_zero] at h2
  exact h2.congr fun t => (disp_const_closed h0 h1 hrec t).symm

/-- Woodford (2003), (2.20), and Cochrane (2023), §20.3, p. 485: started at Cochrane's
stationary dispersion, Woodford's dispersion stays there. -/
theorem disp_const_stationary {α π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) {Δ : ℕ → ℝ}
    (hrec : DispRec α (ZLBWelfare.dispersion α π) Δ fun _ => π) (t : ℕ) :
    Δ t = ZLBWelfare.dispersion α π := by
  rw [disp_const_closed h0 h1 hrec t, sub_self, mul_zero, add_zero]

/-- Woodford (2003), p. 400 (the discounted dispersion, `Sequences.disp_discounted`), at
constant inflation; Cochrane (2023), §20.3, p. 485: `∑ βᵗΔ_t = D/(1 − β) + α(Δ_{−1} − D)/(1 − αβ)`
(genuine `HasSum`). -/
theorem disp_const_discounted {α β Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {Δ : ℕ → ℝ} (hrec : DispRec α Δm1 Δ fun _ => π) :
    HasSum (fun t => β ^ t * Δ t) (ZLBWelfare.dispersion α π / (1 - β) +
      α * (Δm1 - ZLBWelfare.dispersion α π) / (1 - α * β)) := by
  have hab0 : 0 ≤ α * β := mul_nonneg h0 hβ0
  have hab1 : α * β < 1 := by nlinarith
  have hA := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (ZLBWelfare.dispersion α π)
  have hB := (hasSum_geometric_of_lt_one hab0 hab1).mul_left
    (α * (Δm1 - ZLBWelfare.dispersion α π))
  convert hA.add hB using 1
  · funext t
    rw [disp_const_closed h0 h1 hrec t, mul_pow, pow_succ]
    ring
  · rw [div_eq_mul_inv, div_eq_mul_inv]

/-- Woodford (2003), Proposition 6.3, p. 400 (the weight `α/((1 − α)(1 − αβ))` on `π²` in the
welfare loss), and Cochrane (2023), §20.3, p. 485: at constant inflation Woodford's discounted
average dispersion is Cochrane's stationary dispersion times `(1 − α)/(1 − αβ)`, which is
`απ²/((1 − α)(1 − αβ))`, plus a term `(1 − β)αΔ_{−1}/(1 − αβ)` independent of `π`. -/
theorem disp_const_avg {α β Δm1 π : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {Δ : ℕ → ℝ} (hrec : DispRec α Δm1 Δ fun _ => π) :
    (1 - β) * ∑' t, β ^ t * Δ t =
        ZLBWelfare.dispersion α π * ((1 - α) / (1 - α * β)) +
          (1 - β) * α * Δm1 / (1 - α * β) ∧
      ZLBWelfare.dispersion α π * ((1 - α) / (1 - α * β)) =
        α * π ^ 2 / ((1 - α) * (1 - α * β)) := by
  have hab : 0 < 1 - α * β := by nlinarith
  have h1' : 0 < 1 - α := by linarith
  have hb' : 0 < 1 - β := by linarith
  have hne : 1 - α * β ≠ 0 := hab.ne'
  have hne2 : 1 - β ≠ 0 := hb'.ne'
  rw [(disp_const_discounted h0 h1 hβ0 hβ1 hrec).tsum_eq]
  refine ⟨?_, ?_⟩
  · have hu : (1 - α * β) * (1 - α * β)⁻¹ = 1 := mul_inv_cancel₀ hne
    have hv : (1 - β) * (1 - β)⁻¹ = 1 := mul_inv_cancel₀ hne2
    simp only [div_eq_mul_inv]
    linear_combination ZLBWelfare.dispersion α π * hv - ZLBWelfare.dispersion α π * hu
  · rw [ZLBWelfare.dispersion_eq h0 h1]
    field_simp

/-- Cochrane (2023), §20.3, pp. 484–485 (`ZLBWelfare.zlb_better_iff`, corrected E9), in
**Woodford's (2003) welfare criterion** (discounted dispersion, Proposition 6.3, p. 400): with
the same initial dispersion and discount factor, the zero-bound steady state `Π_L = β`
(constant inflation `log β`) has strictly lower discounted dispersion than the target
`Π* ≥ 1` iff `1 < βΠ*`. -/
theorem woodford_zlb_better_iff {α β Δm1 Pstar : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hP : 1 ≤ Pstar) {ΔL ΔS : ℕ → ℝ}
    (hL : DispRec α Δm1 ΔL fun _ => Real.log β) (hS : DispRec α Δm1 ΔS fun _ => Real.log Pstar) :
    (1 - β) * ∑' t, β ^ t * ΔL t < (1 - β) * ∑' t, β ^ t * ΔS t ↔ 1 < β * Pstar := by
  have hab : 0 < 1 - α * β := by nlinarith
  have hc : 0 < (1 - α) / (1 - α * β) := div_pos (by linarith) hab
  rw [(disp_const_avg h0.le h1 hβ0.le hβ1 hL).1, (disp_const_avg h0.le h1 hβ0.le hβ1 hS).1,
    add_lt_add_iff_right, mul_lt_mul_iff_left₀ hc]
  exact ZLBWelfare.zlb_better_iff h0 h1 hβ0 hβ1.le hP

/-- Woodford (2003), (2.24), p. 402 (the quadratic loss `π² + λx²`), and Cochrane (2023),
§20.3, p. 485: at a steady state with inflation `π` and `x̄ = (1 − β)π/κ`, the discounted
average loss `(1 − β)∑ βᵗ(π² + λx̄²)` is `ZLBWelfare.ssLoss`. -/
theorem quadLoss_steady {lam β κ π : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    HasSum (fun t => β ^ t * (π ^ 2 + lam * ((1 - β) * π / κ) ^ 2))
        (ZLBWelfare.ssLoss lam β κ π / (1 - β)) ∧
      (1 - β) * ∑' t, β ^ t * (π ^ 2 + lam * ((1 - β) * π / κ) ^ 2) =
        ZLBWelfare.ssLoss lam β κ π := by
  have h := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (ZLBWelfare.ssLoss lam β κ π)
  have hb : (1 : ℝ) - β ≠ 0 := by linarith
  have h' : HasSum (fun t => β ^ t * (π ^ 2 + lam * ((1 - β) * π / κ) ^ 2))
      (ZLBWelfare.ssLoss lam β κ π / (1 - β)) := by
    convert h using 1
    · funext t; unfold ZLBWelfare.ssLoss; ring
    · rw [div_eq_inv_mul]
  refine ⟨h', ?_⟩
  rw [h'.tsum_eq]
  field_simp

/-- Galí (2015), p. 146 (correction C5 of the Galí Chapter 5 project, `ZLBDiscretion.deflGap`),
restated: the deflationary steady-state output gap `x̄ = −(1 − β)ρ/κ`; Cochrane (2023), §20.3,
p. 485. -/
noncomputable def deflGap (β κ ρ : ℝ) : ℝ := -((1 - β) * ρ / κ)

/-- Galí (2015), p. 146 (the deflationary steady state `π = −ρ`, `i = 0`, of the Galí Chapter 5
project's `deflation_discEq`), with Galí's `ρ ≡ −log β`, **is Cochrane's (2023) zero-bound
steady state `Π_L = β`** (§20.3, p. 484, `ZLBWelfare.zlb_steady_state`): the constant path solves
the Phillips curve and has `i = 0`, its inflation is `log β = log Π_L`, and its output gap is the
steady-state Phillips-curve gap `(1 − β) log β / κ` (`ZLBWelfare.ss_phillips_iff`). -/
theorem gali_deflation_steady {β κ σ ρ : ℝ} (hβ0 : 0 < β) (hκ : κ ≠ 0)
    (hρ : ρ = -Real.log β) :
    (∀ t, NKPC β κ (fun _ => deflGap β κ ρ) (fun _ => -ρ) t) ∧
      (∀ t, impliedRate σ (fun _ => ρ) (fun _ => deflGap β κ ρ) (fun _ => -ρ) t = 0) ∧
      -ρ = Real.log β ∧ Real.exp (-ρ) = β ∧
      (∀ PL, PL = β * (1 + 0) → PL = Real.exp (-ρ)) ∧
      deflGap β κ ρ = (1 - β) * Real.log β / κ := by
  have hl : -ρ = Real.log β := by rw [hρ, neg_neg]
  have he : Real.exp (-ρ) = β := by rw [hl, Real.exp_log hβ0]
  refine ⟨fun t => ?_, fun t => ?_, hl, he, fun PL hPL => ?_, ?_⟩
  · unfold NKPC deflGap
    field_simp
    ring
  · unfold impliedRate
    ring
  · rw [ZLBWelfare.zlb_steady_state hPL rfl, he]
  · unfold deflGap
    rw [← hl]
    ring

/-- Cochrane (2023), §20.3, pp. 484–485 (`ZLBWelfare.zlb_worse_iff`), applied to Galí's (2015)
setting, whose target is zero inflation (`Π* = 1`): Galí's deflationary steady state
(`π = −ρ = log β`, `0 < β < 1`) has strictly more relative-price dispersion, a strictly larger
Woodford discounted dispersion (same initial dispersion), and a strictly larger steady-state
quadratic loss than the target. -/
theorem gali_deflation_worse {α β Δm1 lam κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hlam : 0 ≤ lam) {ΔL ΔS : ℕ → ℝ}
    (hL : DispRec α Δm1 ΔL fun _ => Real.log β) (hS : DispRec α Δm1 ΔS fun _ => 0) :
    ZLBWelfare.dispersion α 0 < ZLBWelfare.dispersion α (Real.log β) ∧
      (1 - β) * ∑' t, β ^ t * ΔS t < (1 - β) * ∑' t, β ^ t * ΔL t ∧
      ZLBWelfare.ssLoss lam β κ 0 < ZLBWelfare.ssLoss lam β κ (Real.log β) := by
  have hlog : Real.log β < 0 := Real.log_neg hβ0 hβ1
  have hd : ZLBWelfare.dispersion α 0 < ZLBWelfare.dispersion α (Real.log β) := by
    have := (ZLBWelfare.zlb_worse_iff h0 h1 hβ0 hβ1.le (le_refl (1 : ℝ))).2 (by linarith)
    rwa [Real.log_one] at this
  have hab : 0 < 1 - α * β := by nlinarith
  have hc : 0 < (1 - α) / (1 - α * β) := div_pos (by linarith) hab
  refine ⟨hd, ?_, ?_⟩
  · rw [(disp_const_avg h0.le h1 hβ0.le hβ1 hL).1, (disp_const_avg h0.le h1 hβ0.le hβ1 hS).1,
      add_lt_add_iff_right, mul_lt_mul_iff_left₀ hc]
    exact hd
  · rw [ZLBWelfare.ssLoss_lt_iff hlam, abs_zero, abs_pos]
    exact hlog.ne


/-! ## Galí's verification theorem (restated from the Galí Chapter 5 project) -/

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (14), p. 135: `γ (ϑ(1 + β) + κ²) = ϑ`. -/
theorem gam_mul_denom {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    gam β κ ϑ * (ϑ * (1 + β) + κ ^ 2) = ϑ := by
  unfold gam
  have : 0 < ϑ * (1 + β) + κ ^ 2 := by positivity
  field_simp

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136: `4βγ² < 1`, so `δ` is real (for every `κ`). -/
theorem four_beta_gam_sq_lt_one {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    4 * β * gam β κ ϑ ^ 2 < 1 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hle := gam_mul_le (κ := κ) hβ0 hϑ
  have h1 : (gam β κ ϑ * (1 + β)) ^ 2 ≤ 1 := by
    have : 0 ≤ gam β κ ϑ * (1 + β) := by positivity
    nlinarith
  have h2 : 0 < gam β κ ϑ ^ 2 * (1 - β) ^ 2 := by
    have : 0 < 1 - β := by linarith
    positivity
  nlinarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136: the square root `s = Real.sqrt (1 − 4βγ²)` satisfies `s² = 1 − 4βγ²`. -/
theorem sqrt_sq_eq {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2) ^ 2 = 1 - 4 * β * gam β κ ϑ ^ 2 :=
  Real.sq_sqrt (by linarith [four_beta_gam_sq_lt_one (κ := κ) hβ0 hβ1 hϑ])

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136: `δ · 2γβ = 1 − Real.sqrt (1 − 4βγ²)`. -/
theorem del_mul {β κ ϑ : ℝ} (hβ0 : 0 < β) (hϑ : 0 < ϑ) :
    del β κ ϑ * (2 * gam β κ ϑ * β) = 1 - Real.sqrt (1 - 4 * β * gam β κ ϑ ^ 2) := by
  have := gam_pos (κ := κ) hβ0 hϑ
  unfold del
  field_simp

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), (15), p. 136 and footnote 4: `δ` is a root of `γβδ² − δ + γ = 0`, the
undetermined-coefficients condition for `p̂_t = δ p̂_{t−1} + b u_t` to solve (14). -/
theorem del_quad {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    gam β κ ϑ * β * del β κ ϑ ^ 2 - del β κ ϑ + gam β κ ϑ = 0 := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hδ := del_mul (κ := κ) hβ0 hϑ
  have hs2 := sqrt_sq_eq (κ := κ) hβ0 hβ1 hϑ
  set g := gam β κ ϑ
  set s := Real.sqrt (1 - 4 * β * g ^ 2)
  set d := del β κ ϑ
  have h4 : (4 * g * β) * (g * β * d ^ 2 - d + g) = 0 := by
    linear_combination (2 * g * β * d + (1 - s) - 2) * hδ + hs2
  rcases mul_eq_zero.1 h4 with h | h
  · exfalso; have : 0 < 4 * g * β := by positivity
    linarith
  · exact h

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 143 (key identity, used for (15) and (24)): `κ²δ/ϑ = (1 − δ)(1 − βδ)`. -/
theorem kappa_sq_del {β κ ϑ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) :
    κ ^ 2 * del β κ ϑ / ϑ = (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
  have hg := gam_pos (κ := κ) hβ0 hϑ
  have hq := del_quad (κ := κ) hβ0 hβ1 hϑ
  have hm := gam_mul_denom (κ := κ) hβ0 hϑ
  rw [div_eq_iff hϑ.ne']
  apply mul_left_cancel₀ hg.ne'
  linear_combination del β κ ϑ * hm - ϑ * hq

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: `lag f (t + 1) = f t`. -/
@[simp] theorem lag_succ (f : ℕ → ℝ) (t : ℕ) : lag f (t + 1) = f t := rfl

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: `lag f 0 = 0` (the initial conditions `ξ₁,₋₁ = ξ₂,₋₁ = 0`). -/
@[simp] theorem lag_zero (f : ℕ → ℝ) : lag f 0 = 0 := rfl

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (35), p. 149: `π_t + ξ₁,t − ξ₁,t−1 − ξ₂,t−1/(βσ) = 0`. -/
def FOC35 (β σ : ℝ) (π ξ1 ξ2 : ℕ → ℝ) (t : ℕ) : Prop :=
  π t + ξ1 t - lag ξ1 t - lag ξ2 t / (β * σ) = 0

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: the KKT system of the commitment problem — feasibility, the FOCs
(35)–(36) with `ξ₁,₋₁ = ξ₂,₋₁ = 0`, and the slackness conditions `ξ₂ ≥ 0`, `ξ₂ i = 0`. -/
def KKT (β κ σ ϑ : ℝ) (rn x π ξ1 ξ2 : ℕ → ℝ) : Prop :=
  Feasible β κ σ rn x π ∧ ∀ t, FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t ∧ 0 ≤ ξ2 t ∧
    ξ2 t * impliedRate σ rn x π t = 0

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: the Lagrangian identity (summation by parts). For a direction
`(dx, dπ)` satisfying the linearised Phillips curve, the first variation of the truncated loss
equals the inequality-multiplier terms plus a boundary term. -/
theorem lagrangian_identity {β κ σ ϑ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    {x π ξ1 ξ2 dx dπ : ℕ → ℝ}
    (h35 : ∀ t, FOC35 β σ π ξ1 ξ2 t) (h36 : ∀ t, FOC36 β κ ϑ x ξ1 ξ2 t)
    (hd : ∀ t, dπ t = β * dπ (t + 1) + κ * dx t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (π t * dπ t + ϑ * x t * dx t) =
      ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * (dx (s + 1) + dπ (s + 1) / σ - dx s)) -
        β ^ T * ξ2 T * dx T - β ^ (T + 1) * ξ1 T * dπ (T + 1) := by
  induction T with
  | zero =>
    have a := h35 0
    have b := h36 0
    simp only [FOC35, FOC36, lag_zero, zero_div, sub_zero] at a b
    simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty, pow_zero,
      pow_one, one_mul, zero_sub]
    linear_combination dπ 0 * a + dx 0 * b - ξ1 0 * hd 0
  | succ T ih =>
    have a := h35 (T + 1)
    have b := h36 (T + 1)
    simp only [FOC35, FOC36, lag_succ] at a b
    have e1 : β ^ (T + 1) * (ξ2 T / (β * σ)) = β ^ T * ξ2 T / σ := by
      rw [pow_succ]; field_simp
    have e2 : β ^ (T + 1) * (ξ2 T / β) = β ^ T * ξ2 T := by
      rw [pow_succ]; field_simp
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    linear_combination β ^ (T + 1) * dπ (T + 1) * a + β ^ (T + 1) * dx (T + 1) * b -
      β ^ (T + 1) * ξ1 (T + 1) * hd (T + 1) + dπ (T + 1) * e1 + dx (T + 1) * e2

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: if `∑ β^t a_t²` is summable-small (`β^t a_t² → 0`) and `0 ≤ β < 1`,
then `β^t |a_t| → 0`. -/
theorem tendsto_pow_mul_abs {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) {a : ℕ → ℝ}
    (h : Filter.Tendsto (fun t => β ^ t * a t ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t => β ^ t * |a t|) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun t => (β ^ t + β ^ t * a t ^ 2) / 2) Filter.atTop
      (nhds ((0 + 0) / 2)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).add h).div_const 2
  rw [add_zero, zero_div] at hg
  refine squeeze_zero (fun t => by positivity) (fun t => ?_) hg
  have hp : 0 ≤ β ^ t := pow_nonneg hβ t
  have : |a t| ≤ (1 + a t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|a t| - 1), sq_abs (a t)]
  nlinarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: SUFFICIENCY of the KKT system (Lagrangian + convexity). If `(x, π)`
satisfies the KKT system with bounded multipliers and has finite loss, then for every feasible
`(y, q)` with finite loss, `loss (x, π) + ∑ β^t ((q_t − π_t)² + ϑ (y_t − x_t)²) ≤ loss (y, q)`. -/
theorem kkt_sufficient {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q)) :
    Summable (fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2)) ∧
      loss β ϑ x π + ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) ≤
        loss β ϑ y q := by
  obtain ⟨hF, hK⟩ := hK
  obtain ⟨C, hC⟩ := hb
  set D : ℕ → ℝ := fun t => β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hsy.add hs).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2 ≤
        2 * ((q t ^ 2 + ϑ * y t ^ 2) + (π t ^ 2 + ϑ * x t ^ 2)) := by
      nlinarith [sq_nonneg (q t + π t), sq_nonneg (y t + x t)]
    nlinarith
  refine ⟨hDs, ?_⟩
  -- the boundary terms vanish
  have hD_lim := hDs.tendsto_atTop_zero
  have hdx : Filter.Tendsto (fun t => β ^ t * |y t - x t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      (by simpa using hD_lim.div_const ϑ))
    simp only [hDdef]
    rw [le_div_iff₀ hϑ]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [sq_nonneg (q t - π t)]
  have hdπ : Filter.Tendsto (fun t => β ^ t * |q t - π t|) Filter.atTop (nhds 0) := by
    refine tendsto_pow_mul_abs hβ.le hβ1 (squeeze_zero (fun t => by positivity) (fun t => ?_)
      hD_lim)
    simp only [hDdef]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [mul_nonneg hp (mul_nonneg hϑ.le (sq_nonneg (y t - x t)))]
  set b : ℕ → ℝ := fun T => C * (β ^ T * |y T - x T|) +
    C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) with hbdef
  have hb_lim : Filter.Tendsto (fun T => -(2 * b T)) Filter.atTop (nhds 0) := by
    have := ((hdx.const_mul C).add ((hdπ.comp (Filter.tendsto_add_atTop_nat 1)).const_mul C))
    simpa [hbdef] using (this.const_mul 2).neg
  -- partial sums
  have hlimL : Filter.Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t)
      Filter.atTop (nhds (loss β ϑ y q - loss β ϑ x π - ∑' t, D t)) := by
    have h1 := hsy.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := hs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    have h3 := hDs.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
    exact (h1.sub h2).sub h3
  have hineq : ∀ T, -(2 * b T) ≤ ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
      ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t := by
    intro T
    have hsplit : ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ y q t -
        ∑ t ∈ Finset.range (T + 1), lossTerm β ϑ x π t - ∑ t ∈ Finset.range (T + 1), D t =
        2 * ∑ t ∈ Finset.range (T + 1),
          β ^ t * (π t * (q t - π t) + ϑ * x t * (y t - x t)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [lossTerm, hDdef]
      ring
    have hd : ∀ t, q t - π t = β * (q (t + 1) - π (t + 1)) + κ * (y t - x t) := by
      intro t
      have h1 := (hy t).1
      have h2 := (hF t).1
      unfold NKPC at h1 h2
      linarith
    have hid := lagrangian_identity hβ.ne' hσ.ne' (fun t => (hK t).1) (fun t => (hK t).2.1)
      (dx := fun t => y t - x t) (dπ := fun t => q t - π t) hd T
    rw [hsplit, hid]
    have hsum : 0 ≤ ∑ s ∈ Finset.range T, β ^ s * (ξ2 s * ((y (s + 1) - x (s + 1)) +
        (q (s + 1) - π (s + 1)) / σ - (y s - x s))) := by
      refine Finset.sum_nonneg fun s _ => mul_nonneg (pow_nonneg hβ.le s) ?_
      have hslack : ξ2 s * (ups1 σ rn x π s - x s) = 0 := by
        have h := (hK s).2.2.2
        rw [impliedRate_eq hσ.ne'] at h
        rw [mul_left_comm] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hσ.ne'
        · exact h'
      have hfy : 0 ≤ ξ2 s * (ups1 σ rn y q s - y s) :=
        mul_nonneg (hK s).2.2.1 (by linarith [(hy s).2])
      have e : ξ2 s * ((y (s + 1) - x (s + 1)) + (q (s + 1) - π (s + 1)) / σ - (y s - x s)) =
          ξ2 s * (ups1 σ rn y q s - y s) - ξ2 s * (ups1 σ rn x π s - x s) := by
        unfold ups1; ring
      rw [e, hslack]
      linarith
    have hC1 := (hC T).2
    have hC2 := (hC T).1
    have hp : 0 ≤ β ^ T := pow_nonneg hβ.le T
    have hp1 : 0 ≤ β ^ (T + 1) := pow_nonneg hβ.le (T + 1)
    have k1 : |β ^ T * ξ2 T * (y T - x T)| ≤ C * (β ^ T * |y T - x T|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp]
      have := abs_nonneg (y T - x T)
      nlinarith [mul_nonneg (sub_nonneg.mpr hC1) (mul_nonneg hp this)]
    have k2 : |β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1))| ≤
        C * (β ^ (T + 1) * |q (T + 1) - π (T + 1)|) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp1]
      have := abs_nonneg (q (T + 1) - π (T + 1))
      nlinarith [mul_nonneg (sub_nonneg.mpr hC2) (mul_nonneg hp1 this)]
    have k3 := le_abs_self (β ^ T * ξ2 T * (y T - x T))
    have k4 := le_abs_self (β ^ (T + 1) * ξ1 T * (q (T + 1) - π (T + 1)))
    simp only [hbdef]
    linarith
  have := le_of_tendsto_of_tendsto' hb_lim hlimL hineq
  unfold loss at this ⊢
  linarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: a KKT path with bounded multipliers and finite loss is optimal. -/
theorem kkt_optimal {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π)) :
    Optimal β κ σ ϑ rn x π := by
  refine ⟨hK.1, hs, fun y q hy hsy => ?_⟩
  obtain ⟨hDs, hle⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have : 0 ≤ ∑' t, β ^ t * ((q t - π t) ^ 2 + ϑ * (y t - x t) ^ 2) :=
    tsum_nonneg fun t => by positivity
  linarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 149: UNIQUENESS — a KKT path (bounded multipliers, finite loss) is the
only feasible path with finite loss whose loss is no larger. -/
theorem kkt_unique {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    {rn x π ξ1 ξ2 : ℕ → ℝ} (hK : KKT β κ σ ϑ rn x π ξ1 ξ2)
    (hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C) (hs : Summable (lossTerm β ϑ x π))
    {y q : ℕ → ℝ} (hy : Feasible β κ σ rn y q) (hsy : Summable (lossTerm β ϑ y q))
    (hle : loss β ϑ y q ≤ loss β ϑ x π) : y = x ∧ q = π := by
  obtain ⟨hDs, hle2⟩ := kkt_sufficient hβ hβ1 hσ hϑ hK hb hs hy hsy
  have hz := eq_zero_of_tsum_nonpos (fun t => by positivity) hDs (by linarith)
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  · have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), pp. 149–150: the multiplier `ξ₁,t_C+1+k = δ^k ξ` (from (38) and (42)). -/
noncomputable def postXi (β κ ϑ ξ : ℝ) (k : ℕ) : ℝ := del β κ ϑ ^ k * ξ

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (37), p. 149: `π_t + ξ₁,t − ξ₁,t−1 = 0` after liftoff. -/
theorem post_eq37 (β κ ϑ ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k + postXi β κ ϑ ξ (k + 1) - postXi β κ ϑ ξ k = 0 := by
  unfold postPi postXi; ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (38), p. 149: `ϑ x_t − κ ξ₁,t = 0` after liftoff. -/
theorem post_eq38 {β κ ϑ : ℝ} (hϑ : ϑ ≠ 0) (ξ : ℝ) (k : ℕ) :
    ϑ * postX β κ ϑ ξ k - κ * postXi β κ ϑ ξ (k + 1) = 0 := by
  unfold postX postXi; field_simp; ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), eq. (39), p. 149: the Phillips curve `π_t = β π_{t+1} + κ x_t` after liftoff. -/
theorem post_eq39 {β κ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (ξ : ℝ) (k : ℕ) :
    postPi β κ ϑ ξ k = β * postPi β κ ϑ ξ (k + 1) + κ * postX β κ ϑ ξ k := by
  have key : κ ^ 2 * del β κ ϑ =
      ϑ * (1 - del β κ ϑ) * (1 - β * del β κ ϑ) := by
    have h := kappa_sq_del (κ := κ) hβ hβ1 hϑ
    rw [div_eq_iff hϑ.ne'] at h
    linear_combination h
  unfold postPi postX
  set δ := del β κ ϑ
  field_simp
  linear_combination (-(δ ^ k * ξ)) * key

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152: after liftoff the implied rate is
`i_{t_C+2+k} = ρ + (1 − δ)(1 − σκ/ϑ) δ^{k+1} ξ`. -/
theorem post_rate {β κ σ ϑ ρ η : ℝ} (hϑ : ϑ ≠ 0) {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ}
    {ξ : ℝ} (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k)
    (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k) (k : ℕ) :
    impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) =
      ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (k + 1) * ξ := by
  unfold impliedRate
  rw [natRate_of_lt (by omega), show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hx, hπ]
  unfold postX postPi
  field_simp
  ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152: the infinitely many conditions `i_t ≥ 0`, `t ≥ t_C + 2`, reduce to the
single condition `i_{t_C+2} ≥ 0` (the rate moves monotonically towards `ρ > 0`). -/
theorem post_rate_nonneg {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ} {ξ : ℝ}
    (hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k) (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k)
    (h0 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) (k : ℕ) :
    0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + k + 2) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  have e0 : impliedRate σ (natRate ρ η tZ) x π (tC + 2) =
      ρ + (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (0 + 1) * ξ :=
    post_rate hϑ.ne' htC hx hπ 0
  rw [e0] at h0
  rw [post_rate hϑ.ne' htC hx hπ k]
  set A := (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * ξ with hA
  have hk : (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (k + 1) * ξ =
      A * del β κ ϑ ^ (k + 1) := by rw [hA]; ring
  have h0' : (1 - del β κ ϑ) * (1 - σ * κ / ϑ) * del β κ ϑ ^ (0 + 1) * ξ =
      A * del β κ ϑ := by rw [hA]; ring
  rw [hk]
  rw [h0'] at h0
  have hp : del β κ ϑ ^ (k + 1) ≤ del β κ ϑ := by
    rw [pow_succ']
    exact mul_le_of_le_one_right hδ0.le (pow_le_one₀ hδ0.le hδ1.le)
  have hp0 : 0 ≤ del β κ ϑ ^ (k + 1) := pow_nonneg hδ0.le _
  rcases le_or_gt 0 A with hA0 | hA0
  · have := mul_nonneg hA0 hp0; linarith
  · nlinarith

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152: one backward step of (48)/(49) gives the Phillips curve and `i_t = 0`. -/
theorem backStep_nkpc_rate {β κ σ e : ℝ} (hσ : σ ≠ 0) {rn x π : ℕ → ℝ} {t : ℕ}
    (h : (x t, π t) = backStep β κ σ e (x (t + 1), π (t + 1))) (hr : rn t = -e) :
    NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
  rw [Prod.ext_iff] at h
  obtain ⟨hx, hπ⟩ := h
  simp only [backStep] at hx hπ
  refine ⟨?_, ?_⟩
  · unfold NKPC; rw [hπ, hx]; ring
  · unfold impliedRate; rw [hr, hx]; field_simp; ring

/-- Restated from the Galí Chapter 5 project; Cochrane (2023), §20.2.4, p. 479.
Galí (2015), p. 152, VERIFICATION THEOREM for the algorithm. Guess `t_C ≥ t_Z`. Suppose the
candidate path satisfies (48) on `[0, t_Z]`, (49) on `(t_Z, t_C]`, (50) for `t ≤ t_C + 1`, the
Phillips curve at `t_C + 1` (i.e. (46)), `ξ₂,t_C+1 = 0`, and follows (42)–(43) (with
`ξ₁,t = δ^{t−t_C−1} ξ₁,t_C+1`, `ξ₂,t = 0`) after `t_C + 1`. If the sign conditions
`ξ₂,t ≥ 0` hold on `[0, t_C]` and `i ≥ 0` at `t_C + 1` and `t_C + 2`, then the candidate
satisfies the KKT system, is optimal, keeps `i_t = 0` on `[0, t_C]` (with `i ≥ 0` everywhere),
and is the unique optimal path. -/
theorem algorithm_verification {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC)
    {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hi1 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (hi2 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) :
    KKT β κ σ ϑ (natRate ρ η tZ) x π ξ1 ξ2 ∧ Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      (∀ t, t ≤ tC → impliedRate σ (natRate ρ η tZ) x π t = 0) ∧
      (∀ t, 0 ≤ impliedRate σ (natRate ρ η tZ) x π t) ∧
      (∀ y q, Feasible β κ σ (natRate ρ η tZ) y q → Summable (lossTerm β ϑ y q) →
        loss β ϑ y q ≤ loss β ϑ x π → y = x ∧ q = π) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1) with hξ
  set rn := natRate ρ η tZ with hrn
  have hξ1post : ∀ k, ξ1 (tC + 1 + k) = postXi β κ ϑ ξ k := by
    intro k
    rcases k with _ | k
    · simp [postXi, hξ]
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.1
  have hξ2post : ∀ k, ξ2 (tC + 1 + k) = 0 := by
    intro k
    rcases k with _ | k
    · simpa using hξ2
    · rw [show tC + 1 + (k + 1) = tC + k + 2 by omega]; exact (hpost k).2.2.2
  have hbind : ∀ t, t ≤ tC → NKPC β κ x π t ∧ impliedRate σ rn x π t = 0 := by
    intro t ht
    rcases le_or_gt t tZ with h | h
    · exact backStep_nkpc_rate hσ.ne' (h48 t h) (by rw [hrn, natRate_of_le h])
    · exact backStep_nkpc_rate hσ.ne' (h49 t h ht) (by rw [hrn, natRate_of_lt h, neg_neg])
  have hx : ∀ k, x (tC + k + 2) = postX β κ ϑ ξ k := fun k => (hpost k).1
  have hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ ξ k := fun k => (hpost k).2.1
  have hrate : ∀ t, 0 ≤ impliedRate σ rn x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · rw [(hbind t ht).2]
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact hi1
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        exact post_rate_nonneg hβ hβ1 hκ hϑ hρ htC hx hπ hi2 k
  have hnkpc : ∀ t, NKPC β κ x π t := by
    intro t
    rcases le_or_gt t tC with ht | ht
    · exact (hbind t ht).1
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · rw [← h]; exact h46
      · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
        unfold NKPC
        rw [show tC + k + 2 + 1 = tC + (k + 1) + 2 by omega, hx, hπ, hπ]
        exact post_eq39 hβ hβ1 hϑ ξ k
  have hK : KKT β κ σ ϑ rn x π ξ1 ξ2 := by
    refine ⟨feasible_of_rate hσ fun t => ⟨hnkpc t, hrate t⟩, fun t => ?_⟩
    rcases le_or_gt t (tC + 1) with ht | ht
    · refine ⟨(h50 t ht).1, (h50 t ht).2, ?_, ?_⟩
      · rcases le_or_gt t tC with h | h
        · exact hsign t h
        · rw [show t = tC + 1 by omega, hξ2]
      · rcases le_or_gt t tC with h | h
        · rw [(hbind t h).2, mul_zero]
        · rw [show t = tC + 1 by omega, hξ2, zero_mul]
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + k + 2 := ⟨t - tC - 2, by omega⟩
      have e : tC + k + 2 = (tC + 1 + k) + 1 := by omega
      have l1 : lag ξ1 (tC + k + 2) = postXi β κ ϑ ξ k := by rw [e, lag_succ, hξ1post]
      have l2 : lag ξ2 (tC + k + 2) = 0 := by rw [e, lag_succ, hξ2post]
      have x1 : ξ1 (tC + k + 2) = postXi β κ ϑ ξ (k + 1) := (hpost k).2.2.1
      have x2 : ξ2 (tC + k + 2) = 0 := (hpost k).2.2.2
      refine ⟨?_, ?_, by rw [x2], by rw [x2, zero_mul]⟩
      · unfold FOC35
        rw [l1, l2, x1, hπ, zero_div, sub_zero]
        exact post_eq37 β κ ϑ ξ k
      · unfold FOC36
        rw [l2, x1, x2, hx, zero_div, sub_zero, add_zero]
        exact post_eq38 hϑ.ne' ξ k
  -- bounded multipliers
  have hb : ∃ C, ∀ t, |ξ1 t| ≤ C ∧ |ξ2 t| ≤ C := by
    refine ⟨∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) + |ξ|, fun t => ?_⟩
    have hS : 0 ≤ ∑ s ∈ Finset.range (tC + 1), (|ξ1 s| + |ξ2 s|) :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hξ0 := abs_nonneg ξ
    rcases le_or_gt t tC with ht | ht
    · have hle := Finset.single_le_sum (f := fun s => |ξ1 s| + |ξ2 s|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
      have a1 := abs_nonneg (ξ1 t)
      have a2 := abs_nonneg (ξ2 t)
      constructor <;> linarith
    · obtain ⟨k, rfl⟩ : ∃ k, t = tC + 1 + k := ⟨t - tC - 1, by omega⟩
      rw [hξ1post, hξ2post, abs_zero]
      refine ⟨?_, by linarith⟩
      unfold postXi
      rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0.le k)]
      have : del β κ ϑ ^ k * |ξ| ≤ |ξ| :=
        mul_le_of_le_one_left hξ0 (pow_le_one₀ hδ0.le hδ1.le)
      linarith
  -- finite loss
  have hs : Summable (lossTerm β ϑ x π) := by
    refine (summable_nat_add_iff (tC + 2)).mp ?_
    have e : (fun n => lossTerm β ϑ x π (n + (tC + 2))) = fun n =>
        β ^ (tC + 2) * (((1 - del β κ ϑ) * ξ) ^ 2 +
          ϑ * (κ * del β κ ϑ * ξ / ϑ) ^ 2) *
          (β * del β κ ϑ ^ 2) ^ n := by
      funext n
      rw [lossTerm, show n + (tC + 2) = tC + n + 2 by omega, hx, hπ]
      unfold postX postPi
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left _
  refine ⟨hK, kkt_optimal hβ hβ1 hσ hϑ hK hb hs, fun t ht => (hbind t ht).2, hrate,
    fun y q hy hsy hle => kkt_unique hβ hβ1 hσ hϑ hK hb hs hy hsy hle⟩

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), §5.4.2, p. 152: **discretion is strictly
worse than commitment**, from the algorithm's conditions alone. Under the hypotheses of
`algorithm_verification` and `ξ₁,t_C+1 > 0`, the candidate is the commitment optimum and the
discretionary path has strictly larger loss (and strictly lower `x_t`, `π_t` at every date,
`comm_gt_disc`). -/
theorem comm_loss_lt_alg {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hϑ : 0 < ϑ) (hρ : 0 < ρ) {tZ tC : ℕ} (htC : tZ ≤ tC)
    {x π ξ1 ξ2 : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (h50 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t ∧ FOC36 β κ ϑ x ξ1 ξ2 t)
    (h46 : NKPC β κ x π (tC + 1)) (hξ2 : ξ2 (tC + 1) = 0)
    (hpost : ∀ k, x (tC + k + 2) = postX β κ ϑ (ξ1 (tC + 1)) k ∧
      π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k ∧
      ξ1 (tC + k + 2) = postXi β κ ϑ (ξ1 (tC + 1)) (k + 1) ∧ ξ2 (tC + k + 2) = 0)
    (hsign : ∀ t, t ≤ tC → 0 ≤ ξ2 t)
    (hi1 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 1))
    (hi2 : 0 ≤ impliedRate σ (natRate ρ η tZ) x π (tC + 2)) (hξ : 0 < ξ1 (tC + 1)) :
    Optimal β κ σ ϑ (natRate ρ η tZ) x π ∧
      loss β ϑ x π < loss β ϑ (discX β κ σ η tZ) (discPi β κ σ η tZ) := by
  have hopt := (algorithm_verification hβ hβ1 hκ hσ hϑ hρ htC h48 h49 h50 h46 hξ2 hpost hsign
    hi1 hi2).2.1
  exact ⟨hopt, comm_loss_lt hβ hβ1 hκ hσ hϑ hρ htC h48 h49 (h50 (tC + 1) le_rfl).2 h46 hξ2
    (fun k => ⟨(hpost k).1, (hpost k).2.1⟩) (hsign tC le_rfl) hξ hopt⟩


/-! ## The sign of `ξ₁,t_C+1` and the lift-off date at the optimum -/

/-- Galí (2015), eq. (35), p. 149; Cochrane (2023), §20.2.4, p. 479: summing (35) with
`ξ₋₁ = 0`, `ξ₁,N = (βσ)⁻¹ ∑_{s<N} ξ₂,s − p_N` with `p_N = ∑_{s≤N} π_s` the price level
(`p₋₁ = 0`). -/
theorem xi1_eq {β σ : ℝ} {π ξ1 ξ2 : ℕ → ℝ} {N : ℕ}
    (h35 : ∀ t, t ≤ N → FOC35 β σ π ξ1 ξ2 t) :
    ξ1 N = (∑ s ∈ Finset.range N, ξ2 s) / (β * σ) - ∑ s ∈ Finset.range (N + 1), π s := by
  induction N with
  | zero =>
    have h := h35 0 le_rfl
    unfold FOC35 at h
    simp only [lag_zero, zero_div, sub_zero] at h
    simp only [Finset.range_zero, Finset.sum_empty, zero_div, zero_add, Finset.sum_range_one,
      zero_sub]
    linarith
  | succ N ih =>
    have h := h35 (N + 1) le_rfl
    unfold FOC35 at h
    simp only [lag_succ] at h
    have hN := ih (fun t ht => h35 t (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun s => π s) (N + 1), add_div]
    linarith

/-- Galí (2015), pp. 149–150; Cochrane (2023), §20.2.4, p. 479: **the precise condition for
`ξ₁,t_C+1 > 0`** (the sign Galí assumes for (42)–(43)): it holds iff the price level at lift-off
is below `(βσ)⁻¹ ∑_{s≤t_C} ξ₂,s`, i.e. below its long-run level (`longrun_price`). -/
theorem xi_pos_iff {β σ : ℝ} {π ξ1 ξ2 : ℕ → ℝ} {tC : ℕ}
    (h35 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t) :
    0 < ξ1 (tC + 1) ↔
      ∑ s ∈ Finset.range (tC + 2), π s < (∑ s ∈ Finset.range (tC + 1), ξ2 s) / (β * σ) := by
  rw [xi1_eq h35]
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (41), p. 150; Cochrane (2023), §20.2.4, p. 479 (price-level targeting under
commitment): under (35) up to lift-off and the closed form (43) after it, the price level
converges to `(βσ)⁻¹ ∑_{s≤t_C} ξ₂,s`, which is `≥ 0` (the initial level) when `ξ₂ ≥ 0`. -/
theorem longrun_price {β κ σ ϑ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ)
    {π ξ1 ξ2 : ℕ → ℝ} {tC : ℕ} (h35 : ∀ t, t ≤ tC + 1 → FOC35 β σ π ξ1 ξ2 t)
    (hπ : ∀ k, π (tC + k + 2) = postPi β κ ϑ (ξ1 (tC + 1)) k) :
    Tendsto (fun k => ∑ s ∈ Finset.range (tC + 2 + k), π s) atTop
      (𝓝 ((∑ s ∈ Finset.range (tC + 1), ξ2 s) / (β * σ))) := by
  have hδ0 := del_pos (κ := κ) hβ hϑ
  have hδ1 := (del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne'
  set ξ := ξ1 (tC + 1)
  set P := ∑ s ∈ Finset.range (tC + 2), π s
  have hsum : ∀ k, ∑ s ∈ Finset.range (tC + 2 + k), π s = P + ξ * (1 - del β κ ϑ ^ k) := by
    intro k
    induction k with
    | zero => simp [P]
    | succ k ih =>
      rw [show tC + 2 + (k + 1) = tC + 2 + k + 1 by omega, Finset.sum_range_succ, ih,
        show tC + 2 + k = tC + k + 2 by omega, hπ k]
      unfold postPi
      ring
  have hlim : Tendsto (fun k => P + ξ * (1 - del β κ ϑ ^ k)) atTop (𝓝 (P + ξ * (1 - 0))) :=
    tendsto_const_nhds.add
      (((tendsto_pow_atTop_nhds_zero_of_lt_one hδ0.le hδ1).const_sub 1).const_mul ξ)
  have hx := xi1_eq h35
  rw [sub_zero, mul_one] at hlim
  have e : P + ξ = (∑ s ∈ Finset.range (tC + 1), ξ2 s) / (β * σ) := by
    simp only [ξ, P]; rw [hx]; ring
  rw [e] at hlim
  exact hlim.congr fun k => (hsum k).symm

/-- Galí (2015), eqs. (42)–(43), p. 150; Cochrane (2023), p. 479: with `ξ₁,t_C+1 < 0` output and
inflation are strictly NEGATIVE at every date after lift-off (the signs of (42)–(43) reverse). -/
theorem post_neg {β κ ϑ ξ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hϑ : 0 < ϑ) (hξ : ξ < 0)
    (k : ℕ) : postX β κ ϑ ξ k < 0 ∧ postPi β κ ϑ ξ k < 0 := by
  have h0 := del_pos (κ := κ) hβ hϑ
  have h1 : 0 < 1 - del β κ ϑ := by linarith [(del_lt_one_iff (κ := κ) hβ hβ1 hϑ).mpr hκ.ne']
  have hp : 0 < del β κ ϑ ^ k := pow_pos h0 k
  have hp1 : 0 < del β κ ϑ ^ (k + 1) := pow_pos h0 _
  unfold postX postPi
  constructor
  · have : κ * del β κ ϑ ^ (k + 1) * ξ < 0 := mul_neg_of_pos_of_neg (by positivity) hξ
    exact div_neg_of_neg_of_pos this hϑ
  · exact mul_neg_of_pos_of_neg (by positivity) hξ

/-- Cochrane (2023), §20.2.4, p. 479, Galí (2015), §5.4.2: the commitment path lies strictly
above the delayed-lift-off path with the same lift-off date on `[0, t_C]` whenever its lift-off
state is weakly positive and nonzero — no assumption on the sign of `ξ₁,t_C+1`. -/
theorem comm_gt_delay_of_state {β κ σ ρ η : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    {tZ tC : ℕ} {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (hx : 0 ≤ x (tC + 1)) (hp : 0 ≤ π (tC + 1)) (hs : 0 < x (tC + 1) ∨ 0 < π (tC + 1))
    (t : ℕ) (ht : t ≤ tC) :
    (delayPath β κ σ ρ η tZ (tC + 1) t).1 < x t ∧ (delayPath β κ σ ρ η tZ (tC + 1) t).2 < π t := by
  have hd : delayPath β κ σ ρ η tZ (tC + 1) (tC + 1) = (0, 0) := delay_after le_rfl
  exact zr_strict hβ.le hκ hσ (e := fun t => -natRate ρ η tZ t) (N := tC + 1)
    (p := fun t => (x t, π t)) (fun s hs => comm_step h48 h49 s hs)
    (fun s hs => delay_step hs) (by rw [hd]; exact hx) (by rw [hd]; exact hp)
    (by rw [hd]; exact hs) t (by omega)

/-- Cochrane (2023), §20.2.4, p. 479: hence, with a weakly positive nonzero lift-off state, the
commitment path is strictly above discretion on the whole zero-rate spell `[0, t_C]`. -/
theorem comm_gt_disc_of_state {β κ σ ρ η : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 < ρ)
    {tZ tC : ℕ} (htC : tZ ≤ tC) {x π : ℕ → ℝ}
    (h48 : ∀ t, t ≤ tZ → (x t, π t) = backStep β κ σ η (x (t + 1), π (t + 1)))
    (h49 : ∀ t, tZ < t → t ≤ tC → (x t, π t) = backStep β κ σ (-ρ) (x (t + 1), π (t + 1)))
    (hx : 0 ≤ x (tC + 1)) (hp : 0 ≤ π (tC + 1)) (hs : 0 < x (tC + 1) ∨ 0 < π (tC + 1))
    (t : ℕ) (ht : t ≤ tC) : discX β κ σ η tZ t < x t ∧ discPi β κ σ η tZ t < π t := by
  have a := comm_gt_delay_of_state hβ hκ hσ (ρ := ρ) h48 h49 hx hp hs t ht
  have b := delay_le_of_le (η := η) hβ.le hκ hσ hρ (tZ := tZ) le_rfl
    (show tZ + 1 ≤ tC + 1 by omega) t
  rw [delay_eq_disc] at b
  exact ⟨b.1.trans_lt a.1, b.2.trans_lt a.2⟩

/-! ### An exact parameter point: lift-off at the end of the shock and `ξ₁,t_C+1 < 0` -/

/-- Galí (2015), (15), p. 136; Cochrane (2023), p. 479: at `β = 9/10`, `κ = 1/10`,
`ϑ = 1/819` the coefficient `δ` is exactly `1/10` (`γ = 100/1009`,
`√(1 − 4βγ²) = 991/1009`). -/
theorem del_cex : del (9 / 10) (1 / 10) (1 / 819) = 1 / 10 := by
  unfold del gam
  have hs : Real.sqrt (1 - 4 * (9 / 10) * ((1 / 819) / ((1 / 819) * (1 + 9 / 10) +
      (1 / 10) ^ 2)) ^ 2) = 991 / 1009 := by
    rw [show (1 - 4 * (9 / 10) * ((1 / 819) / ((1 / 819) * (1 + 9 / 10) + (1 / 10) ^ 2)) ^ 2 :
      ℝ) = (991 / 1009) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs]
  norm_num

/-- Cochrane (2023), §20.2.4, p. 479: the multiplier `ξ₁,1` at the exact point. -/
noncomputable def cexXi : ℝ := -743471 / 4255023510

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: the output gap of the exact point
(`t_Z = t_C = 0`): `x₀, x₁`, then (42). -/
noncomputable def cexX (t : ℕ) : ℝ :=
  if t = 0 then -2226861 / 472780390 else if t = 1 then 23344139 / 4727803900
  else postX (9 / 10) (1 / 10) (1 / 819) cexXi (t - 2)

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: inflation at the exact point: `π₀, π₁`, then
(43). -/
noncomputable def cexPi (t : ℕ) : ℝ :=
  if t = 0 then -7281 / 47278039 else if t = 1 then 166529 / 472780390
  else postPi (9 / 10) (1 / 10) (1 / 819) cexXi (t - 2)

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: the multiplier `ξ₁` at the exact point. -/
noncomputable def cexXi1 (t : ℕ) : ℝ :=
  if t = 0 then 7281 / 47278039 else postXi (9 / 10) (1 / 10) (1 / 819) cexXi (t - 1)

/-- Galí (2015), §5.4.2; Cochrane (2023), p. 479: the ZLB multiplier `ξ₂` at the exact point
(positive at date 0 only). -/
noncomputable def cexXi2 (t : ℕ) : ℝ := if t = 0 then 1000 / 47278039 else 0

/-- Cochrane (2023), p. 479: `ξ₁,1 = ξ` at the exact point. -/
theorem cexXi1_one : cexXi1 1 = cexXi := by
  simp [cexXi1, postXi]

/-- Galí (2015), p. 152 (`algorithm_verification` at an exact point); Cochrane (2023), §20.2.4,
p. 479: with `β = 9/10`, `κ = 1/10`, `σ = 1`, `ϑ = 1/819` (so `δ = 1/10`), `ρ = 1/10`,
`η = 1/100`, `t_Z = 0`, the path `cexX`, `cexPi` with multipliers `cexXi1`, `cexXi2` passes the
algorithm with `t_C = t_Z = 0`: it is the commitment optimum, and the unique one. -/
theorem cex_optimal :
    Optimal (9 / 10) (1 / 10) 1 (1 / 819) (natRate (1 / 10) (1 / 100) 0) cexX cexPi ∧
      (∀ y q, Optimal (9 / 10) (1 / 10) 1 (1 / 819) (natRate (1 / 10) (1 / 100) 0) y q →
        y = cexX ∧ q = cexPi) ∧
      impliedRate 1 (natRate (1 / 10) (1 / 100) 0) cexX cexPi 0 = 0 := by
  have hd := del_cex
  have hv := algorithm_verification (β := 9 / 10) (κ := 1 / 10) (σ := 1) (ϑ := 1 / 819)
    (ρ := 1 / 10) (η := 1 / 100) (tZ := 0) (tC := 0) (x := cexX) (π := cexPi) (ξ1 := cexXi1)
    (ξ2 := cexXi2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) le_rfl
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      simp only [cexX, cexPi, backStep]
      norm_num)
    (fun t h1 h2 => absurd h2 (by omega))
    (fun t ht => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · simp only [FOC35, FOC36, lag_zero, cexX, cexPi, cexXi1, cexXi2]
        norm_num
      · simp only [FOC35, FOC36, lag_succ, cexX, cexPi, cexXi1, cexXi2, postXi, cexXi]
        norm_num)
    (by simp only [NKPC, cexX, cexPi, postPi, hd, cexXi]; norm_num)
    (by simp [cexXi2])
    (fun k => by
      rw [cexXi1_one]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [cexX, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega]
      · simp only [cexPi, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega]
      · simp only [cexXi1, show 0 + k + 2 ≠ 0 by omega, ↓reduceIte,
          show 0 + k + 2 - 1 = k + 1 by omega]
      · simp [cexXi2])
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      simp only [cexXi2]; norm_num)
    (by
      simp only [impliedRate, natRate, cexX, cexPi, postX, postPi, hd, cexXi]
      norm_num)
    (by
      simp only [impliedRate, natRate, cexX, cexPi, postX, postPi, hd, cexXi]
      norm_num)
  obtain ⟨-, hopt, hzero, -, -⟩ := hv
  exact ⟨hopt, fun y q h => (optimal_unique (by norm_num) (by norm_num) h hopt),
    hzero 0 le_rfl⟩

/-- Cochrane (2023), §20.2.4, p. 479, against Galí (2015), §5.4.2 (correction): at the exact
point the commitment optimum **lifts off at the end of the shock**, `t_C = t_Z = 0`: the rate
is `0` at date 0 and strictly positive at every later date. So "keeping the rate at zero beyond
the end of the shock" (`t_C > t_Z`) is not a property of every commitment optimum. -/
theorem cex_liftoff_at_shock_end :
    impliedRate 1 (natRate (1 / 10) (1 / 100) 0) cexX cexPi 0 = 0 ∧
      ∀ t, 1 ≤ t → 0 < impliedRate 1 (natRate (1 / 10) (1 / 100) 0) cexX cexPi t := by
  have hd := del_cex
  refine ⟨cex_optimal.2.2, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t 2 with h | h
  · obtain rfl : t = 1 := by omega
    simp only [impliedRate, natRate, cexX, cexPi, postX, postPi, hd, cexXi]
    norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, t = 0 + k + 2 := ⟨t - 2, by omega⟩
    rw [post_rate (β := 9 / 10) (κ := 1 / 10) (σ := 1) (ϑ := 1 / 819) (ρ := 1 / 10)
      (η := 1 / 100) (by norm_num) le_rfl (ξ := cexXi)
      (fun k => by simp only [cexX, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega])
      (fun k => by simp only [cexPi, show 0 + k + 2 ≠ 0 by omega, show 0 + k + 2 ≠ 1 by omega,
          ↓reduceIte, show 0 + k + 2 - 2 = k by omega]) k, hd]
    have hp : (0 : ℝ) < (1 / 10) ^ (k + 1) := by positivity
    unfold cexXi
    nlinarith

/-- Cochrane (2023), §20.2.4, p. 479, against Galí (2015), eqs. (42)–(43), p. 150 (correction):
at the exact point the commitment optimum has `ξ₁,t_C+1 < 0`, and **output and inflation are
strictly negative at every date after lift-off** (inflation strictly below the discretionary
path for `t ≥ 2`); the sign hypothesis `ξ₁,t_C+1 > 0` of `comm_gt_disc` cannot be dropped.
At the same time the lift-off state is positive, so the optimum still lies strictly above discretion
during the zero-rate spell (`comm_gt_disc_of_state`). -/
theorem cex_xi_neg :
    cexXi1 1 < 0 ∧ (∀ t, 2 ≤ t → cexX t < 0 ∧ cexPi t < 0) ∧
      (∀ t, 2 ≤ t → cexPi t < discPi (9 / 10) (1 / 10) 1 (1 / 100) 0 t) ∧
      discX (9 / 10) (1 / 10) 1 (1 / 100) 0 0 < cexX 0 ∧
      discPi (9 / 10) (1 / 10) 1 (1 / 100) 0 0 < cexPi 0 := by
  have hneg : cexXi < 0 := by unfold cexXi; norm_num
  have hpost : ∀ t, 2 ≤ t → cexX t < 0 ∧ cexPi t < 0 := by
    intro t ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
    simp only [cexX, cexPi, show k + 2 ≠ 0 by omega, show k + 2 ≠ 1 by omega, ↓reduceIte,
      Nat.add_sub_cancel]
    exact post_neg (by norm_num) (by norm_num) (by norm_num) (by norm_num) hneg k
  refine ⟨by rw [cexXi1_one]; exact hneg, hpost, fun t ht => ?_, ?_, ?_⟩
  · have hz := zlbPath_of_lt (β := 9 / 10) (κ := 1 / 10) (σ := 1) (η := 1 / 100)
      (sT := ((0 : ℝ), (0 : ℝ))) (show 0 < t by omega)
    unfold discPi
    rw [hz]
    exact (hpost t ht).2
  · simp only [discX, zlbPath, le_refl, ↓reduceIte, Nat.sub_zero, zero_add, backState,
      backStep, cexX]
    norm_num
  · simp only [discPi, zlbPath, le_refl, ↓reduceIte, Nat.sub_zero, zero_add, backState,
      backStep, cexPi]
    norm_num

end Cochrane.ZeroBound.LinksGaliWoodford
