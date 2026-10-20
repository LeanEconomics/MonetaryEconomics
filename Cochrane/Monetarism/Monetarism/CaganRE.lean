/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.ForwardSolution
import Monetarism.ExpectationsFiniteTree
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interest-elastic money demand and multiple equilibria (Cagan with rational expectations)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.2, pp. 436–438,
eqs. (19.4)–(19.8). Adapted from the Woodford Chapter 2 project (`MoneyGrowth`, the Cagan
equation (A.28)–(A.29)); everything holds for an arbitrary `ExpectationSystem`.

Notation: `a = αv > 0` is the semi-elasticity of money demand (the book's `αv`), `y`, `r`
constants, `m`, `p` log money and log price level, `θ = (1 + a)/a > 1` (`theta`), and the
forcing `x_t = m_t − y + ar` (`forcing`).

## Main results

* (19.4) `eq194_iff_log` (levels ⇔ logs); (19.5) `md_fisher_iff_cagan`, `cagan_iff_expect`,
  `cagan_iff_solves` (the forward form `p_t = θ⁻¹E_tp_{t+1} + (1 − θ⁻¹)x_t`), `theta_gt_one`.
* (19.6) `steady_state_iff`, `steady_state_strictMono_r` (higher `r`, higher `p`).
* (19.7) `eq197_iff`; the solution family `caganFamily`, `caganFamily_closed`
  (`p_t − p̄ = θᵗ(p₀ − p̄) + ∑ θ^{t−j}δ_j`), `caganFamily_solves` (every `p₀` and every
  expectational error with `E_tδ_{t+1} = 0`), `eq_caganFamily` (every solution is a member);
  explosions: `pf_path`, `pf_explodes`, `expected_path`, `expected_explodes`,
  `bounded_iff_steady`; multiplicity: `pf_solutions_uncountable`, `coin_sunspot_solves`,
  `coin_sunspot_ne_steady` (sunspots under genuine uncertainty).
* (19.8) `eq198_finite`, `eq198` (the limit term exists iff the series converges), for bounded
  money `eq198_bounded_money`, `limit_zero_iff_bounded` (the limit term vanishes iff the
  solution is the bounded one), `bounded_existsUnique`.
* Fiscal theory selects `P₀` (p. 437): `fiscal_selects_P0`, `fiscal_path_existsUnique`,
  `fiscal_path_bounded_iff` (the selected path is explosive except for one value of `B₋₁`).
* Stochastic version (p. 438): `innov`, `valuation_split`, `stochastic_selection` (the
  valuation equation picks unexpected inflation; with expected inflation it determines `B_t`).
-/

namespace Cochrane.Monetarism.CaganRE

open Filter Topology
open Cochrane.Monetarism.ForwardSolution (Solves iterate_A15 summable_A16 existsUnique_bounded
  solves_adapted E_of_known forwardSeries_bounded_abs)
open Cochrane.Monetarism.ExpectationsFiniteTree (coinSystem coinShock coinShock_measurable
  coinShock_mean_zero coinTree)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (19.4)–(19.5) -/

/-- Cochrane (2023), eq. (19.4), p. 436: money demand `M_t = P_t y V^{−αi_t}` holds in levels iff
it holds in logs, `m_t − p_t − y = −αi_t v` (`v = log V`). -/
theorem eq194_iff_log {M P Y V α i : ℝ} (hM : 0 < M) (hP : 0 < P) (hY : 0 < Y) (hV : 0 < V) :
    M = P * Y * V ^ (-α * i) ↔
      Real.log M - Real.log P - Real.log Y = -α * i * Real.log V := by
  have hR : 0 < P * Y * V ^ (-α * i) := by positivity
  have hlog : Real.log (P * Y * V ^ (-α * i)) =
      Real.log P + Real.log Y + -α * i * Real.log V := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hP.ne' hY.ne',
      Real.log_rpow hV]
  constructor
  · intro h
    rw [h, hlog]
    ring
  · intro h
    have : Real.log M = Real.log (P * Y * V ^ (-α * i)) := by rw [hlog]; linarith
    rw [← Real.exp_log hM, ← Real.exp_log hR, this]

/-- Cochrane (2023), eq. (19.4), p. 436, in logs: `m_t − p_t − y = −a i_t` with `a = αv`. -/
def MoneyDemand (a y : ℝ) (m p i : ℕ → Ω → ℝ) : Prop := ∀ t ω, m t ω - p t ω - y = -a * i t ω

/-- Cochrane (2023), p. 436: the Fisher equation `i_t = r + E_tp_{t+1} − p_t`. -/
def Fisher (r : ℝ) (p i : ℕ → Ω → ℝ) : Prop := ∀ t ω, i t ω = r + 𝔼.E t (p (t + 1)) ω - p t ω

/-- Cochrane (2023), eq. (19.5), p. 436: `m_t − p_t − y = −a(r + E_tp_{t+1} − p_t)`. -/
def Cagan (a y r : ℝ) (m p : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, m t ω - p t ω - y = -a * (r + 𝔼.E t (p (t + 1)) ω - p t ω)

/-- Cochrane (2023), (19.4)–(19.5), p. 436: money demand and the Fisher equation hold iff the
Cagan equation (19.5) and the Fisher equation hold. -/
theorem md_fisher_iff_cagan {a y r : ℝ} {m p i : ℕ → Ω → ℝ} :
    MoneyDemand a y m p i ∧ Fisher 𝔼 r p i ↔ Cagan 𝔼 a y r m p ∧ Fisher 𝔼 r p i := by
  constructor
  · rintro ⟨hmd, hf⟩
    exact ⟨fun t ω => by rw [hmd t ω, hf t ω], hf⟩
  · rintro ⟨hc, hf⟩
    exact ⟨fun t ω => by rw [hc t ω, hf t ω], hf⟩

/-- Cochrane (2023), p. 437: `θ ≡ (1 + αv)/(αv)`. -/
noncomputable def theta (a : ℝ) : ℝ := (1 + a) / a

/-- Cochrane (2023), p. 437: `θ > 1` for `a = αv > 0`. -/
theorem theta_gt_one {a : ℝ} (ha : 0 < a) : 1 < theta a := by
  unfold theta
  rw [one_lt_div ha]
  linarith

/-- Cochrane (2023), p. 437: `θ⁻¹ = a/(1 + a)`. -/
theorem theta_inv {a : ℝ} : (theta a)⁻¹ = a / (1 + a) := by
  unfold theta
  rw [inv_div]

/-- Cochrane (2023), p. 437: `|θ⁻¹| < 1` for `a > 0`. -/
theorem abs_theta_inv_lt_one {a : ℝ} (ha : 0 < a) : |(theta a)⁻¹| < 1 := by
  rw [theta_inv, abs_of_pos (by positivity), div_lt_one (by linarith)]
  linarith

/-- Cochrane (2023), eq. (19.5), second line, p. 436:
`E_tp_{t+1} = ((1 + a)/a)p_t − (m_t − y)/a − r`. -/
theorem cagan_iff_expect {a y r : ℝ} (ha : a ≠ 0) {m p : ℕ → Ω → ℝ} :
    Cagan 𝔼 a y r m p ↔
      ∀ t ω, 𝔼.E t (p (t + 1)) ω = theta a * p t ω - (m t ω - y) / a - r := by
  unfold theta
  constructor
  · intro h t ω
    have := h t ω
    field_simp
    linarith
  · intro h t ω
    have := h t ω
    field_simp at this
    linarith

/-- Cochrane (2023), (19.8), p. 437: the forcing `x_t = m_t − y + ar` (`ar` = the book's
`αvr`). -/
def forcing (a y r : ℝ) (m : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => m t ω - y + a * r

/-- Cochrane (2023), eq. (19.8), first lines, p. 437: the Cagan equation is the forward equation
`p_t = θ⁻¹E_tp_{t+1} + (1 − θ⁻¹)x_t`. -/
theorem cagan_iff_solves {a y r : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} :
    Cagan 𝔼 a y r m p ↔
      Solves 𝔼 (theta a)⁻¹ (fun t => (1 - (theta a)⁻¹) • forcing a y r m t) p := by
  rw [theta_inv]
  have h1 : (1 + a) ≠ 0 := by linarith
  constructor
  · intro h t
    funext ω
    have := h t ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, forcing]
    field_simp
    linarith
  · intro h t ω
    have := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, forcing] at this
    field_simp at this
    linarith

/-- Cochrane (2023), (19.8), p. 437: the forcing is adapted when money is. -/
theorem forcing_adapted {a y r : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m) :
    𝔼.Adapted (fun t => (1 - (theta a)⁻¹) • forcing a y r m t) := fun t => by
  change 𝔼.E t ((1 - (theta a)⁻¹) • forcing a y r m t) = (1 - (theta a)⁻¹) • forcing a y r m t
  have h : forcing a y r m t = m t + fun _ => -y + a * r := by
    funext ω
    simp only [forcing, Pi.add_apply]
    ring
  rw [map_smul, h, map_add, hm t, 𝔼.const]

/-! ### (19.6)–(19.7): constant money -/

/-- Cochrane (2023), eq. (19.6), p. 436: the steady-state price level `p̄ = m − y + αvr`. -/
def pbar (a y r mbar : ℝ) : ℝ := mbar - y + a * r

/-- Cochrane (2023), eq. (19.6), p. 436: with constant money `m`, a constant price level `c`
solves (19.5) iff `c = m − y + αvr`. -/
theorem steady_state_iff [Nonempty Ω] {a y r mbar c : ℝ} :
    Cagan 𝔼 a y r (fun _ _ => mbar) (fun _ _ => c) ↔ c = pbar a y r mbar := by
  unfold pbar
  have hE : ∀ t ω, 𝔼.E t (fun _ => c) ω = c := fun t ω => by rw [𝔼.const]
  constructor
  · intro h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := h 0 ω
    rw [hE] at this
    linarith
  · intro h t ω
    rw [hE, h]
    ring

/-- Cochrane (2023), p. 436 ("The steady-state price level is higher as the real interest rate
is higher"): `r ↦ m − y + αvr` is strictly increasing for `αv > 0`. -/
theorem steady_state_strictMono_r {a y mbar : ℝ} (ha : 0 < a) :
    StrictMono (fun r => pbar a y r mbar) := fun r r' h => by
  unfold pbar
  nlinarith

/-- Cochrane (2023), eq. (19.7), p. 436: with constant money, the equilibrium price levels are
exactly the processes with `E_tp_{t+1} − p̄ = θ(p_t − p̄)`. -/
theorem eq197_iff {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ} :
    Cagan 𝔼 a y r (fun _ _ => mbar) p ↔
      ∀ t ω, 𝔼.E t (p (t + 1)) ω - pbar a y r mbar = theta a * (p t ω - pbar a y r mbar) := by
  rw [cagan_iff_expect 𝔼 ha.ne']
  unfold theta pbar
  constructor
  · intro h t ω
    rw [h t ω]
    field_simp
    ring
  · intro h t ω
    have := h t ω
    field_simp at this ⊢
    linarith

/-- Cochrane (2023), p. 437: the family `p_0` given and
`p_{t+1} − p̄ = θ(p_t − p̄) + δ_{t+1}`. -/
noncomputable def caganFamily (θ pb : ℝ) (p0 : Ω → ℝ) (δ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => p0
  | t + 1 => fun ω => pb + θ * (caganFamily θ pb p0 δ t ω - pb) + δ (t + 1) ω

omit 𝔼 in
/-- Cochrane (2023), p. 437, the full set of solutions in closed form:
`p_t − p̄ = θᵗ(p_0 − p̄) + ∑_{j=1}^t θ^{t−j}δ_j` (written with `k = t − j`). -/
theorem caganFamily_closed (θ pb : ℝ) (p0 : Ω → ℝ) (δ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    caganFamily θ pb p0 δ t ω =
      pb + θ ^ t * (p0 ω - pb) + ∑ k ∈ Finset.range t, θ ^ k * δ (t - k) ω := by
  induction t with
  | zero => simp [caganFamily]
  | succ t ih =>
    simp only [caganFamily]
    have hs : ∀ k ∈ Finset.range t, θ * (θ ^ k * δ (t - k) ω) =
        θ ^ (k + 1) * δ (t + 1 - (k + 1)) ω := fun k _ => by
      rw [Nat.add_sub_add_right, pow_succ]
      ring
    rw [ih, Finset.sum_range_succ', ← Finset.sum_congr rfl hs, ← Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero, pow_succ]
    ring

/-- Cochrane (2023), p. 437: the family is adapted when `p_0` and `δ` are. -/
theorem caganFamily_adapted {θ pb : ℝ} {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0)
    (hδ : 𝔼.Adapted δ) : 𝔼.Adapted (caganFamily θ pb p0 δ) := by
  intro t
  induction t with
  | zero => exact hp0
  | succ t ih =>
    have h : caganFamily θ pb p0 δ (t + 1) =
        (fun _ => pb - θ * pb) + θ • caganFamily θ pb p0 δ t + δ (t + 1) := by
      funext ω
      simp only [caganFamily, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h, map_add, map_add, map_smul, 𝔼.const, E_of_known 𝔼 (Nat.le_succ t) ih, hδ (t + 1)]

/-- Cochrane (2023), p. 437: one step of the family, conditional expectation:
`E_tp_{t+1} − p̄ = θ(p_t − p̄) + E_tδ_{t+1}`. -/
theorem caganFamily_E_succ {θ pb : ℝ} {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0)
    (hδ : 𝔼.Adapted δ) (t : ℕ) :
    𝔼.E t (caganFamily θ pb p0 δ (t + 1)) =
      (fun _ => pb - θ * pb) + θ • caganFamily θ pb p0 δ t + 𝔼.E t (δ (t + 1)) := by
  have h : caganFamily θ pb p0 δ (t + 1) =
      (fun _ => pb - θ * pb) + θ • caganFamily θ pb p0 δ t + δ (t + 1) := by
    funext ω
    simp only [caganFamily, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, map_add, map_add, map_smul, 𝔼.const, caganFamily_adapted 𝔼 hp0 hδ t]

/-- Cochrane (2023), p. 437 ("the model restricts `E_tδ_{t+1} = 0`, but the expectational error
`δ_{t+1}` can take any value ex-post"): for every initial `p_0` known at date 0 and every adapted
`δ` with `E_tδ_{t+1} = 0`, the family solves (19.5) with constant money. -/
theorem caganFamily_solves {a y r mbar : ℝ} (ha : 0 < a) {p0 : Ω → ℝ} {δ : ℕ → Ω → ℝ}
    (hp0 : 𝔼.E 0 p0 = p0) (hδ : 𝔼.Adapted δ) (hmd : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    Cagan 𝔼 a y r (fun _ _ => mbar) (caganFamily (theta a) (pbar a y r mbar) p0 δ) := by
  rw [eq197_iff 𝔼 ha]
  intro t ω
  rw [caganFamily_E_succ 𝔼 hp0 hδ t, hmd t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- Cochrane (2023), p. 437 ("the full set of solutions"): every solution of (19.5) with
constant money is the member of the family with its own `p_0` and expectational errors
`δ_{t+1} = p_{t+1} − E_tp_{t+1}`, which satisfy `E_tδ_{t+1} = 0`. -/
theorem eq_caganFamily {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) :
    (∀ t, 𝔼.E t (p (t + 1) - 𝔼.E t (p (t + 1))) = 0) ∧
      p = caganFamily (theta a) (pbar a y r mbar) (p 0)
        (fun t => p t - 𝔼.E (t - 1) (p t)) := by
  refine ⟨fun t => by rw [map_sub, 𝔼.E_E_self, sub_self], ?_⟩
  have h197 := (eq197_iff 𝔼 ha).mp hp
  funext t ω
  induction t generalizing ω with
  | zero => rfl
  | succ t ih =>
    simp only [caganFamily, ← ih, Nat.add_sub_cancel, Pi.sub_apply]
    have := h197 t ω
    linarith

/-- Cochrane (2023), p. 437, under perfect foresight: every solution with constant money is
`p_t = p̄ + θᵗ(p_0 − p̄)`. -/
theorem pf_path {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Unit → ℝ}
    (hp : Cagan perfectForesight a y r (fun _ _ => mbar) p) (t : ℕ) :
    p t () = pbar a y r mbar + theta a ^ t * (p 0 () - pbar a y r mbar) := by
  have h197 := (eq197_iff perfectForesight ha).mp hp
  induction t with
  | zero => simp
  | succ t ih =>
    have := h197 t ()
    change p (t + 1) () - _ = _ at this
    have e : p (t + 1) () = pbar a y r mbar + theta a * (p t () - pbar a y r mbar) := by
      linarith
    rw [e, ih, pow_succ]
    ring

/-- Cochrane (2023), p. 437 ("The alternative solutions are explosive"): under perfect foresight
every solution with `p_0 ≠ p̄` explodes, `|p_t − p̄| → ∞`. -/
theorem pf_explodes {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Unit → ℝ}
    (hp : Cagan perfectForesight a y r (fun _ _ => mbar) p) (h0 : p 0 () ≠ pbar a y r mbar) :
    Tendsto (fun t => |p t () - pbar a y r mbar|) atTop atTop := by
  have hc : 0 < |p 0 () - pbar a y r mbar| := abs_pos.mpr (sub_ne_zero.mpr h0)
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (theta_gt_one ha)
  refine (hpow.atTop_mul_const hc).congr fun t => ?_
  rw [pf_path ha hp t, add_sub_cancel_left, abs_mul, abs_pow,
    abs_of_pos (by linarith [theta_gt_one ha] : (0 : ℝ) < theta a)]

/-- Cochrane (2023), p. 437 ("At any date for `p_t ≠ p̄`, people expect explosive hyperinflation
or hyperdeflation"): for every solution, `E_0p_t = p̄ + θᵗ(p_0 − p̄)`. -/
theorem expected_path {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) (hp0 : 𝔼.E 0 (p 0) = p 0) (t : ℕ) (ω : Ω) :
    𝔼.E 0 (p t) ω = pbar a y r mbar + theta a ^ t * (p 0 ω - pbar a y r mbar) := by
  have h197 := (eq197_iff 𝔼 ha).mp hp
  induction t generalizing ω with
  | zero => rw [hp0]; simp
  | succ t ih =>
    have hEt : 𝔼.E t (p (t + 1)) = (fun _ => pbar a y r mbar - theta a * pbar a y r mbar) +
        theta a • p t := by
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [h197 t ω']
    rw [← 𝔼.tower (Nat.zero_le t), hEt, map_add, map_smul, 𝔼.const]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [ih ω, pow_succ]
    ring

/-- Cochrane (2023), p. 437: every solution with `p_0 ≠ p̄` (in state `ω`) has an expected price
path that explodes, `|E_0p_t − p̄| → ∞`. -/
theorem expected_explodes {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) (hp0 : 𝔼.E 0 (p 0) = p 0) {ω : Ω}
    (h0 : p 0 ω ≠ pbar a y r mbar) :
    Tendsto (fun t => |𝔼.E 0 (p t) ω - pbar a y r mbar|) atTop atTop := by
  have hc : 0 < |p 0 ω - pbar a y r mbar| := abs_pos.mpr (sub_ne_zero.mpr h0)
  have hpow := tendsto_pow_atTop_atTop_of_one_lt (theta_gt_one ha)
  refine (hpow.atTop_mul_const hc).congr fun t => ?_
  rw [expected_path 𝔼 ha hp hp0 t ω, add_sub_cancel_left, abs_mul, abs_pow,
    abs_of_pos (by linarith [theta_gt_one ha] : (0 : ℝ) < theta a)]

/-- Cochrane (2023), p. 437 ("all but `p_t ≡ p̄` explode"): a solution with constant money is
bounded if and only if it is the steady state. -/
theorem bounded_iff_steady {a y r mbar : ℝ} (ha : 0 < a) {p : ℕ → Ω → ℝ}
    (hp : Cagan 𝔼 a y r (fun _ _ => mbar) p) :
    BoundedProc p ↔ p = fun _ _ => pbar a y r mbar := by
  constructor
  · intro hb
    have hs := (cagan_iff_solves 𝔼 ha).mp hp
    have hss : Cagan 𝔼 a y r (fun _ _ => mbar) (fun _ _ => pbar a y r mbar) := by
      intro t ω
      rw [𝔼.const]
      unfold pbar
      ring
    have hs2 := (cagan_iff_solves 𝔼 ha).mp hss
    exact 𝔼.forward_unique (abs_theta_inv_lt_one ha) hs hs2 hb
      ⟨|pbar a y r mbar|, fun _ _ => le_refl _⟩
  · rintro rfl
    exact ⟨|pbar a y r mbar|, fun _ _ => le_refl _⟩

/-- Cochrane (2023), p. 437 ("There is a family of solutions"): under perfect foresight with
constant money the set of equilibrium price paths is uncountable (one for each `p_0 ∈ ℝ`). -/
theorem pf_solutions_uncountable {a y r mbar : ℝ} (ha : 0 < a) :
    ¬ {p : ℕ → Unit → ℝ | Cagan perfectForesight a y r (fun _ _ => mbar) p}.Countable := by
  intro hcount
  let f : ℝ → ℕ → Unit → ℝ := fun c t _ => pbar a y r mbar + theta a ^ t * (c - pbar a y r mbar)
  have hmaps : Set.MapsTo f Set.univ
      {p : ℕ → Unit → ℝ | Cagan perfectForesight a y r (fun _ _ => mbar) p} := by
    intro c _
    refine (eq197_iff perfectForesight ha).mpr fun t u => ?_
    change f c (t + 1) u - _ = _
    simp only [f, pow_succ]
    ring
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    have := congrFun (congrFun h 0) ()
    simpa [f] using this
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Cochrane (2023), p. 437 (genuine uncertainty): on the coin-flip tree the shocks are
adapted. -/
theorem coinShock_adapted : coinSystem.Adapted coinShock := fun t => by
  funext ω
  rw [coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun ω' h => coinShock_measurable t h

/-- Cochrane (2023), p. 437 ("the expectational error `δ_{t+1}` can take any value ex-post"):
under genuine uncertainty (two coin flips), the family started at `p_0 = p̄` with the coin-flip
errors `δ` solves (19.5) with constant money. -/
theorem coin_sunspot_solves {a y r mbar : ℝ} (ha : 0 < a) :
    Cagan coinSystem a y r (fun _ _ => mbar)
      (caganFamily (theta a) (pbar a y r mbar) (fun _ => pbar a y r mbar) coinShock) :=
  caganFamily_solves coinSystem ha (coinSystem.const 0 _) coinShock_adapted coinShock_mean_zero

/-- Cochrane (2023), p. 437: that sunspot solution is not the steady state even though it starts
at `p̄`: after heads at date 1 the price level is `p̄ + 1`. -/
theorem coin_sunspot_ne_steady (θ pb : ℝ) :
    caganFamily θ pb (fun _ => pb) coinShock 1 (true, true) = pb + 1 := by
  simp [caganFamily, coinShock]

/-! ### (19.8): the forward solution -/

/-- Cochrane (2023), eq. (19.8), p. 437, at a finite horizon `T`:
`p_t = (1 − θ⁻¹)∑_{j<T} θ^{−j}E_tx_{t+j} + θ^{−T}E_tp_{t+T}`. -/
theorem eq198_finite {a y r : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hp : Cagan 𝔼 a y r m p) (t T : ℕ) (ω : Ω) :
    p t ω = (1 - (theta a)⁻¹) * ∑ j ∈ Finset.range T,
      (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω +
      (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω := by
  have h := congrFun (iterate_A15 𝔼 (forcing_adapted 𝔼 hm) ((cagan_iff_solves 𝔼 ha).mp hp)
    t T) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, map_smul] at h
  rw [h, Finset.mul_sum]
  have hs : ∑ j ∈ Finset.range T, (theta a)⁻¹ ^ j *
      ((1 - (theta a)⁻¹) * 𝔼.E t (forcing a y r m (t + j)) ω) =
      ∑ j ∈ Finset.range T, (1 - (theta a)⁻¹) *
        ((theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [hs]
  ring

/-- Cochrane (2023), eq. (19.8), p. 437 ("there is again no reason to set to zero the last
term"): for any solution, the limit term `lim θ^{−T}E_tp_{t+T}` equals `L` if and only if the
forward series `(1 − θ⁻¹)∑θ^{−j}E_tx_{t+j}` converges to `p_t − L`. -/
theorem eq198 {a y r : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hp : Cagan 𝔼 a y r m p) (t : ℕ) (ω : Ω) (L : ℝ) :
    Tendsto (fun T => (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω) atTop (𝓝 L) ↔
      Tendsto (fun T => (1 - (theta a)⁻¹) * ∑ j ∈ Finset.range T,
        (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω) atTop (𝓝 (p t ω - L)) := by
  have hid := eq198_finite 𝔼 ha hm hp t
  constructor
  · intro h
    exact (tendsto_const_nhds.sub h).congr fun T => by rw [hid T ω]; ring
  · intro h
    have h2 := tendsto_const_nhds (x := p t ω) |>.sub h
    rw [sub_sub_cancel] at h2
    exact h2.congr fun T => by rw [hid T ω]; ring

/-- Cochrane (2023), eq. (19.8), p. 437, for bounded money: the series converges for every
solution, so the limit term exists and equals `p_t` minus the forward series. -/
theorem eq198_bounded_money {a y r K : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hK : ∀ t ω, |m t ω| ≤ K) (hp : Cagan 𝔼 a y r m p) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω) atTop
      (𝓝 (p t ω - (1 - (theta a)⁻¹) *
        ∑' j, (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω)) := by
  have hx : ∀ t ω, |forcing a y r m t ω| ≤ K + |y| + |a * r| := fun t ω => by
    simp only [forcing]
    have := hK t ω
    have h1 := abs_add_le (m t ω - y) (a * r)
    have h2 := abs_sub (m t ω) y
    have h3 := abs_mul a r
    linarith
  have hsum := summable_A16 𝔼 (abs_theta_inv_lt_one ha) hx t ω
  rw [eq198 𝔼 ha hm hp t ω, sub_sub_cancel]
  exact hsum.hasSum.tendsto_sum_nat.const_mul _

/-- Cochrane (2023), (19.8), p. 437 ("It is tempting to set the last term … to zero and to
declare a unique forward-looking equilibrium"): for bounded money, the limit term vanishes at
every date and state if and only if the solution is bounded. -/
theorem limit_zero_iff_bounded {a y r K : ℝ} (ha : 0 < a) {m p : ℕ → Ω → ℝ}
    (hm : 𝔼.Adapted m) (hK : ∀ t ω, |m t ω| ≤ K) (hp : Cagan 𝔼 a y r m p) :
    (∀ t ω, Tendsto (fun T => (theta a)⁻¹ ^ T * 𝔼.E t (p (t + T)) ω) atTop (𝓝 0)) ↔
      BoundedProc p := by
  have hθ := abs_theta_inv_lt_one ha
  have hu : ∀ t ω, |((1 - (theta a)⁻¹) • forcing a y r m t) ω| ≤
      |1 - (theta a)⁻¹| * (K + |y| + |a * r|) := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, forcing]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := hK t ω
    have h1 := abs_add_le (m t ω - y) (a * r)
    have h2 := abs_sub (m t ω) y
    have h3 := abs_mul a r
    linarith
  constructor
  · intro h
    have heq : p = 𝔼.forwardSeries (theta a)⁻¹ (fun t => (1 - (theta a)⁻¹) • forcing a y r m t)
        := by
      funext t ω
      have h1 := tendsto_nhds_unique (h t ω) (eq198_bounded_money 𝔼 ha hm hK hp t ω)
      have h2 : p t ω = (1 - (theta a)⁻¹) *
          ∑' j, (theta a)⁻¹ ^ j * 𝔼.E t (forcing a y r m (t + j)) ω := by linarith
      rw [h2, ← tsum_mul_left]
      simp only [ExpectationSystem.forwardSeries, map_smul, Pi.smul_apply, smul_eq_mul]
      exact tsum_congr fun j => by ring
    rw [heq]
    exact forwardSeries_bounded_abs 𝔼 hθ hu
  · rintro ⟨M, hM⟩ t ω
    refine squeeze_zero_norm (a := fun T => |(theta a)⁻¹| ^ T * M) (fun T => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + T)) t ω)
        (pow_nonneg (abs_nonneg _) T)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) hθ).mul_const M

/-- Cochrane (2023), p. 437 ("most papers simply pick the bounded solution"): for bounded adapted
money there is exactly one bounded solution of (19.5). -/
theorem bounded_existsUnique {a y r : ℝ} (ha : 0 < a) {m : ℕ → Ω → ℝ} (hm : 𝔼.Adapted m)
    (hmb : BoundedProc m) : ∃! p, BoundedProc p ∧ Cagan 𝔼 a y r m p := by
  obtain ⟨K, hK⟩ := hmb
  have hub : BoundedProc (fun t => (1 - (theta a)⁻¹) • forcing a y r m t) :=
    ⟨|1 - (theta a)⁻¹| * (K + |y| + |a * r|), fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, forcing]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := hK t ω
      have h1 := abs_add_le (m t ω - y) (a * r)
      have h2 := abs_sub (m t ω) y
      have h3 := abs_mul a r
      linarith⟩
  obtain ⟨p, hp, hu⟩ := existsUnique_bounded 𝔼 (abs_theta_inv_lt_one ha) hub
    (forcing_adapted 𝔼 hm)
  exact ⟨p, ⟨hp.1, (cagan_iff_solves 𝔼 ha).mpr hp.2⟩,
    fun q hq => hu q ⟨hq.1, (cagan_iff_solves 𝔼 ha).mp hq.2⟩⟩

/-! ### Fiscal theory selects `P₀` (pp. 437–438) -/

/-- Cochrane (2023), p. 437 ("This condition picks the one missing element, `P_0`"): with
`B_{−1} > 0` and present value of surpluses `∑βʲs_j = S > 0`, exactly one positive `P_0`
satisfies `B_{−1}/P_0 = ∑βʲs_j`. -/
theorem fiscal_selects_P0 {β B S : ℝ} {s : ℕ → ℝ} (hs : HasSum (fun j => β ^ j * s j) S)
    (hB : 0 < B) (hS : 0 < S) : ∃! P0 : ℝ, 0 < P0 ∧ B / P0 = ∑' j, β ^ j * s j := by
  rw [hs.tsum_eq]
  refine ⟨B / S, ⟨div_pos hB hS, by field_simp⟩, fun P0 hP0 => ?_⟩
  have := hP0.1
  rw [eq_div_iff hS.ne', ← hP0.2]
  field_simp

/-- Cochrane (2023), pp. 437–438 ("we now fully determine the price level"): under perfect
foresight with constant money, there is exactly one price path satisfying (19.5) and the
valuation equation `B_{−1}/P_0 = ∑βʲs_j` (with `P_0 = e^{p_0}`). -/
theorem fiscal_path_existsUnique {a y r mbar β B S : ℝ} {s : ℕ → ℝ} (ha : 0 < a)
    (hs : HasSum (fun j => β ^ j * s j) S) (hB : 0 < B) (hS : 0 < S) :
    ∃! p : ℕ → Unit → ℝ, Cagan perfectForesight a y r (fun _ _ => mbar) p ∧
      B / Real.exp (p 0 ()) = ∑' j, β ^ j * s j := by
  rw [hs.tsum_eq]
  refine ⟨fun t _ => pbar a y r mbar + theta a ^ t * (Real.log (B / S) - pbar a y r mbar),
    ⟨(eq197_iff perfectForesight ha).mpr fun t u => ?_, ?_⟩, fun q hq => ?_⟩
  · change (pbar a y r mbar + theta a ^ (t + 1) * _) - _ = _
    rw [pow_succ]
    ring
  · simp only [pow_zero, one_mul, add_sub_cancel, Real.exp_log (div_pos hB hS)]
    field_simp
  · have h0 : q 0 () = Real.log (B / S) := by
      have h := hq.2
      have hE : Real.exp (q 0 ()) = B / S := by
        rw [eq_div_iff hS.ne', ← h]
        field_simp
      rw [← hE, Real.log_exp]
    funext t u
    rw [pf_path ha hq.1 t, h0]

/-- Cochrane (2023), p. 438 ("The solution picked in this way will generically be one of the
explosive solutions"): the fiscally selected path is bounded if and only if
`B_{−1} = e^{p̄}∑βʲs_j`; for every other value of the initial debt it explodes. -/
theorem fiscal_path_bounded_iff {a y r mbar B S : ℝ} (ha : 0 < a) (hB : 0 < B) (hS : 0 < S)
    {p : ℕ → Unit → ℝ} (hp : Cagan perfectForesight a y r (fun _ _ => mbar) p)
    (hv : B / Real.exp (p 0 ()) = S) :
    BoundedProc p ↔ B = S * Real.exp (pbar a y r mbar) := by
  have hE : Real.exp (p 0 ()) = B / S := by
    rw [eq_div_iff hS.ne', ← hv]
    field_simp
  rw [bounded_iff_steady perfectForesight ha hp]
  constructor
  · intro h
    have h0 := congrFun (congrFun h 0) ()
    rw [h0] at hE
    rw [hE]
    field_simp
  · intro h
    have h0 : p 0 () = pbar a y r mbar := by
      rw [← Real.log_exp (p 0 ()), hE, h, mul_div_cancel_left₀ _ hS.ne', Real.log_exp]
    funext t u
    rw [pf_path ha hp t, h0, sub_self, mul_zero, add_zero]

/-! ### The stochastic version (p. 438) -/

/-- Cochrane (2023), p. 438 (notation `ΔE_{t+1} = E_{t+1} − E_t`): the innovation. -/
def innov (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) x - 𝔼.E t x

/-- Cochrane (2023), p. 438: for variables known at `t + 1`, an equation holds iff it holds in
innovations and in date-`t` expectation. -/
theorem valuation_split {t : ℕ} {X V : Ω → ℝ} (hX : 𝔼.E (t + 1) X = X)
    (hV : 𝔼.E (t + 1) V = V) : X = V ↔ innov 𝔼 t X = innov 𝔼 t V ∧ 𝔼.E t X = 𝔼.E t V := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have e1 : X = innov 𝔼 t X + 𝔼.E t X := by rw [innov, hX]; abel
    have e2 : V = innov 𝔼 t V + 𝔼.E t V := by rw [innov, hV]; abel
    rw [e1, e2, h1, h2]

/-- Cochrane (2023), p. 438: the stochastic valuation equation
`(B_t/P_t)(P_t/P_{t+1}) = E_{t+1}∑βʲs_{t+1+j}` (with `b = B_t/P_t` known at `t`, `R = P_t/P_{t+1}`
known at `t + 1`, `V` the present value known at `t + 1`) holds iff
`b·ΔE_{t+1}R = ΔE_{t+1}V` ("picks unexpected inflation") and `b·E_tR = E_tV`. Hence where
`b ≠ 0` unexpected inflation is `ΔE_{t+1}V/b`, and where `E_tR ≠ 0` real debt sales are
`b = E_tV/E_tR` ("with expected inflation picked by (19.7) determines nominal bond sales"). -/
theorem stochastic_selection (hPO : 𝔼.PullOut) {t : ℕ} {b R V : Ω → ℝ} (hb : 𝔼.E t b = b)
    (hR : 𝔼.E (t + 1) R = R) (hV : 𝔼.E (t + 1) V = V) :
    (b * R = V ↔ b * innov 𝔼 t R = innov 𝔼 t V ∧ b * 𝔼.E t R = 𝔼.E t V) ∧
      (b * R = V → ∀ ω, b ω ≠ 0 → innov 𝔼 t R ω = innov 𝔼 t V ω / b ω) ∧
      (b * R = V → ∀ ω, 𝔼.E t R ω ≠ 0 → b ω = 𝔼.E t V ω / 𝔼.E t R ω) := by
  have hb1 : 𝔼.E (t + 1) b = b := E_of_known 𝔼 (Nat.le_succ t) hb
  have hbR : 𝔼.E (t + 1) (b * R) = b * R := by rw [hPO _ _ _ hb1, hR]
  have hinn : innov 𝔼 t (b * R) = b * innov 𝔼 t R := by
    simp only [innov]
    rw [hPO _ _ _ hb1, hPO _ _ _ hb, mul_sub]
  have hEt : 𝔼.E t (b * R) = b * 𝔼.E t R := hPO _ _ _ hb
  have key : b * R = V ↔ b * innov 𝔼 t R = innov 𝔼 t V ∧ b * 𝔼.E t R = 𝔼.E t V := by
    rw [valuation_split 𝔼 hbR hV, hinn, hEt]
  refine ⟨key, fun h ω hω => ?_, fun h ω hω => ?_⟩
  · have := congrFun ((key.mp h).1) ω
    simp only [Pi.mul_apply] at this
    rw [← this]
    field_simp
  · have := congrFun ((key.mp h).2) ω
    simp only [Pi.mul_apply] at this
    rw [← this]
    field_simp

end Cochrane.Monetarism.CaganRE
