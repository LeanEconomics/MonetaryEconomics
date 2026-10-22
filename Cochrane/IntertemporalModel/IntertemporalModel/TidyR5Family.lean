/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR5BondPrice
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A smooth family of exact nonlinear equilibria and its derivative: the peg

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4, pp. 29–33 (the exact
model under an interest-rate target) and §2.5, pp. 34–37 (the linear model (2.16)–(2.19) as its
linearisation).

`LinearFTMP.fisher_deriv`, `LinearFTMP.linear_217`, `GeneralLinks.isEqm_fisher_log` and
`GeneralLinks.equilibrium_pvNews` show that the exact equations of every equilibrium have the
linear model as their derivatives, along a family assumed to exist. This module **builds** the
family and differentiates it. Shocks of size `ε` hit the steady state: surpluses
`s_t(ε) = s̄ + ε ŝ_t` (`surpFam`) with `ŝ` bounded and adapted, and a rate target `i(ε)` with
`i(0) = 1/β − 1` and `ε ↦ log(1 + i_t(ε))` differentiable at `0` with derivative `î_t` (an
arbitrary family; `rateExp`, `1 + i_t(ε) = β⁻¹ exp(ε î_t)`, is the canonical case).

## Main results

* Explicit solution: `pv_surpFam`, `pvEx_surpFam` (present values are affine in `ε`), so the
  equilibrium is in closed form. On the open interval `famDom` (`|ε| M < s̄`, containing `0`)
  `fam_equilibrium` (for every `ε` the target path `priceFam`, `debtFam` is an exact
  equilibrium, `FiscalMonetary.Equilibrium`) and `fam_unique`, `family_unique` (it is the only
  one, so any family of equilibria is this family).
* `fam_steady`: at `ε = 0` it is the steady state `P_t = B_{−1}/V`, `B_t = B_{−1}`,
  `V = s̄/(1 − β)`.
* Smoothness: `price_contDiffOn`, `debt_contDiffOn`, `infl_contDiffOn` (`C^n` on `famDom` for
  every `n`, including `C^∞` and analytic, whenever the rate family is).
* The derivative: `infl_hasDerivAt` (the derivative at `ε = 0` of inflation
  `π_t(ε) = log(P_t(ε)/P_{t−1}(ε))`, with `P_{−1}` the steady state, is the solution (2.19)
  `LinearFTMP.pegSol î ε_{Σs} π̂_0` of the linear model, with the fiscal shock of (2.17)
  `fiscShock` (news about the present value of surpluses scaled by steady-state debt) and
  `π̂_0 = −pv(ŝ)_0/V`), and `fam_linearization` (the derivative is the unique adapted solution of
  the linear model `LinearFTMP.PegModel` with that `π̂_0`).
* The canonical case: `rateExp` and `exp_family_linearization` (pull-out and
  `FunctionsKnown`), and on every finite event tree `tree_family_linearization`.
-/

namespace Cochrane.IntertemporalModel.TidyR5Family

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The family of economies -/

/-- Cochrane (2023), §2.5, p. 35 (shocks of size `ε` to a constant surplus): the surplus
family `s_t(ε) = s̄ + ε ŝ_t`. -/
def surpFam (sbar : ℝ) (shat : ℕ → Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ :=
  fun t ω => sbar + ε * shat t ω

/-- Cochrane (2023), §2.5, p. 35: the steady-state real value of the debt,
`V = s̄/(1 − β) = ∑ βʲ s̄`. -/
noncomputable def ssV (β sbar : ℝ) : ℝ := (1 - β)⁻¹ * sbar

/-- Cochrane (2023), §2.5, p. 35: the shock sizes `ε` with `|ε| M < s̄`, on which surpluses stay
positive (`M` bounds `|ŝ|`). -/
def famDom (sbar M : ℝ) : Set ℝ := {ε | |ε| * M < sbar}

/-- Cochrane (2023), §2.5, p. 35: the domain of shock sizes is open. -/
theorem famDom_isOpen (sbar M : ℝ) : IsOpen (famDom sbar M) :=
  isOpen_lt ((continuous_abs).mul continuous_const) continuous_const

/-- Cochrane (2023), §2.5, p. 35: the steady state `ε = 0` is in the domain when `s̄ > 0`. -/
theorem zero_mem_famDom {sbar : ℝ} (hs : 0 < sbar) (M : ℝ) : (0 : ℝ) ∈ famDom sbar M := by
  simp only [famDom, Set.mem_ofPred_eq, abs_zero, zero_mul]
  exact hs

/-- Cochrane (2023), §2.5, p. 35: the domain is a neighbourhood of the steady state. -/
theorem famDom_mem_nhds {sbar : ℝ} (hs : 0 < sbar) (M : ℝ) : famDom sbar M ∈ 𝓝 (0 : ℝ) :=
  (famDom_isOpen sbar M).mem_nhds (zero_mem_famDom hs M)

/-! ### Present values are affine in `ε` -/

variable {β sbar M : ℝ} {shat : ℕ → Ω → ℝ}

omit 𝔼 in
/-- Cochrane (2023), eq. (2.7), p. 22: the ex-post discounted sum of the surplus family is
`V + ε ∑ βʲ ŝ_{t+j}` (bounded `ŝ`, `0 ≤ β < 1`). -/
theorem epv_surpFam (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ)
    (t : ℕ) : FiscalMonetary.epv β (surpFam sbar shat ε) t =
      fun ω => ssV β sbar + ε * FiscalMonetary.epv β shat t ω := by
  funext ω
  have h1 : HasSum (fun j : ℕ => β ^ j * sbar) ((1 - β)⁻¹ * sbar) :=
    (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right sbar
  have h2 : Summable fun j => β ^ j * shat (t + j) ω :=
    FiscalMonetary.surplusSummable_of_bounded hβ0 hβ1 hs t ω
  simp only [FiscalMonetary.epv, surpFam, ssV]
  calc ∑' j, β ^ j * (sbar + ε * shat (t + j) ω)
      = ∑' j, (β ^ j * sbar + ε * (β ^ j * shat (t + j) ω)) :=
        tsum_congr fun j => by ring
    _ = (1 - β)⁻¹ * sbar + ε * ∑' j, β ^ j * shat (t + j) ω := by
        rw [h1.summable.tsum_add (h2.mul_left ε), tsum_mul_left, h1.tsum_eq]

/-- Cochrane (2023), eq. (2.7), p. 22: the present value of the surplus family is affine in
`ε`, `PV_t(ε) = V + ε PV_t(ŝ)`. -/
theorem pv_surpFam (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ)
    (t : ℕ) : FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t =
      fun ω => ssV β sbar + ε * FiscalMonetary.pv 𝔼 β shat t ω := by
  unfold FiscalMonetary.pv
  rw [epv_surpFam hβ0 hβ1 hs]
  have e : (fun ω => ssV β sbar + ε * FiscalMonetary.epv β shat t ω) =
      (fun _ => ssV β sbar) + ε • FiscalMonetary.epv β shat t := by
    funext ω
    simp
  rw [e, map_add, map_smul, 𝔼.const]
  funext ω
  simp

/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend present value of the surplus family is
affine in `ε`, `PVex_t(ε) = βV + ε PVex_t(ŝ)`. -/
theorem pvEx_surpFam (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ)
    (t : ℕ) : FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t =
      fun ω => β * ssV β sbar + ε * FiscalMonetary.pvEx 𝔼 β shat t ω := by
  rw [FiscalMonetary.pvEx_eq, pv_surpFam 𝔼 hβ0 hβ1 hs, FiscalMonetary.pvEx_eq]
  have e : (fun ω => ssV β sbar + ε * FiscalMonetary.pv 𝔼 β shat (t + 1) ω) =
      (fun _ => ssV β sbar) + ε • FiscalMonetary.pv 𝔼 β shat (t + 1) := by
    funext ω
    simp
  rw [e, map_add, map_smul, 𝔼.const]
  funext ω
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eq. (2.7), p. 22: `|PV_t(ŝ)| ≤ M/(1 − β)` for `|ŝ| ≤ M`. -/
theorem abs_pv_le (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |FiscalMonetary.pv 𝔼 β shat t ω| ≤ (1 - β)⁻¹ * M := by
  have hb : ∀ ω', |FiscalMonetary.epv β shat t ω'| ≤ (1 - β)⁻¹ * M := by
    intro ω'
    rw [← Real.norm_eq_abs]
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hβ0 hβ1).mul_right M)
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs (t + j) ω') (pow_nonneg hβ0 j)
  exact 𝔼.abs_E_le hb t ω

/-- Cochrane (2023), eq. (2.7), p. 22: the uniform lower bound
`PV_t(ε) ≥ (s̄ − |ε| M)/(1 − β)` for every `ε`. -/
theorem pv_surpFam_ge (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (ε : ℝ)
    (t : ℕ) (ω : Ω) :
    (1 - β)⁻¹ * (sbar - |ε| * M) ≤ FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t ω := by
  rw [pv_surpFam 𝔼 hβ0 hβ1 hs]
  have hY := abs_pv_le 𝔼 hβ0 hβ1 hs t ω
  have hc : 0 ≤ (1 - β)⁻¹ := inv_nonneg.mpr (by linarith)
  have h1 : |ε * FiscalMonetary.pv 𝔼 β shat t ω| ≤ |ε| * ((1 - β)⁻¹ * M) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hY (abs_nonneg ε)
  have h2 := neg_abs_le (ε * FiscalMonetary.pv 𝔼 β shat t ω)
  simp only [ssV]
  nlinarith

/-- Cochrane (2023), eq. (2.7), p. 22: on `famDom` the present value is positive. -/
theorem pv_surpFam_pos (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) (t : ℕ) (ω : Ω) :
    0 < FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t ω := by
  refine lt_of_lt_of_le ?_ (pv_surpFam_ge 𝔼 hβ0 hβ1 hs ε t ω)
  have hε' : |ε| * M < sbar := hε
  have : 0 < (1 - β)⁻¹ := inv_pos.mpr (by linarith)
  exact mul_pos this (by linarith)

/-- Cochrane (2023), eq. (2.15), p. 31: on `famDom` the ex-dividend present value is positive
(`β > 0`). -/
theorem pvEx_surpFam_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) (t : ℕ) (ω : Ω) :
    0 < FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω := by
  have hε' : |ε| * M < sbar := hε
  have hc : 0 < (1 - β)⁻¹ * (sbar - |ε| * M) := mul_pos (inv_pos.mpr (by linarith)) (by linarith)
  have h := FiscalMonetary.pvEx_ge (𝔼 := 𝔼) hβ0.le
    (fun t' ω' => pv_surpFam_ge 𝔼 (sbar := sbar) hβ0.le hβ1 hs ε t' ω') t ω
  exact lt_of_lt_of_le (mul_pos hβ0 hc) h

/-! ### The equilibrium family -/

/-- Cochrane (2023), §2.4.3, p. 31: the price level of the family, the target equilibrium
`FiscalMonetary.pegP` for surpluses `s(ε)` and the rate target `i(ε)`. -/
noncomputable def priceFam (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ)
    (iF : ℝ → ℕ → Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ :=
  FiscalMonetary.pegP 𝔼 β Bm1 (surpFam sbar shat ε) (iF ε)

/-- Cochrane (2023), eq. (2.15), p. 31: the debt sold along the family, `FiscalMonetary.pegB`. -/
noncomputable def debtFam (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ)
    (iF : ℝ → ℕ → Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ :=
  FiscalMonetary.pegB 𝔼 β Bm1 (surpFam sbar shat ε) (iF ε)

/-- Cochrane (2023), §2.5, p. 35: inflation along the family, `π_t(ε) = log(P_t(ε)/P_{t−1}(ε))`,
with `P_{−1} = B_{−1}/V` the steady-state price level. -/
noncomputable def inflFam (β sbar : ℝ) (shat : ℕ → Ω → ℝ) (Bm1 : Ω → ℝ)
    (iF : ℝ → ℕ → Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Real.log (priceFam 𝔼 β sbar shat Bm1 iF ε 0 ω / (Bm1 ω / ssV β sbar))
  | t + 1 => fun ω => Real.log (priceFam 𝔼 β sbar shat Bm1 iF ε (t + 1) ω /
      priceFam 𝔼 β sbar shat Bm1 iF ε t ω)

variable {Bm1 : Ω → ℝ} {iF : ℝ → ℕ → Ω → ℝ}

/-- Cochrane (2023), §2.4.3, p. 31: for every shock size in `famDom` the family is an exact
equilibrium (`FiscalMonetary.Equilibrium`): pull-out, `0 < β < 1`, bounded `ŝ`, positive initial
debt known at `0`, and an adapted rate family exceeding `−1` on the domain. -/
theorem fam_equilibrium (hPO : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω)
    (hiA : ∀ ε ∈ famDom sbar M, 𝔼.Adapted (iF ε))
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω) {ε : ℝ} (hε : ε ∈ famDom sbar M) :
    FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε)
      (debtFam 𝔼 β sbar shat Bm1 iF ε) (priceFam 𝔼 β sbar shat Bm1 iF ε) (iF ε) :=
  FiscalMonetary.peg_equilibrium hPO hBm1 hB (hiA ε hε) (hiG ε hε)
    (pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε) (pvEx_surpFam_pos 𝔼 hβ0 hβ1 hs hε)

/-- Cochrane (2023), p. 33 (determinacy under a target): for every shock size in `famDom`, any
equilibrium with the surpluses `s(ε)` and the target `i(ε)` is the family member. -/
theorem fam_unique (hPO : 𝔼.PullOut) (hβ1 : β < 1) (hβ0 : 0 ≤ β)
    (hs : ∀ t ω, |shat t ω| ≤ M) {ε : ℝ} (hε : ε ∈ famDom sbar M) {B P : ℕ → Ω → ℝ}
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε) B P (iF ε)) :
    P = priceFam 𝔼 β sbar shat Bm1 iF ε ∧ B = debtFam 𝔼 β sbar shat Bm1 iF ε :=
  FiscalMonetary.peg_unique hPO (fun t ω => (pv_surpFam_pos 𝔼 hβ0 hβ1 hs hε t ω).ne') h

/-- Cochrane (2023), §§2.4–2.5, pp. 33–35: **uniqueness of the family**: any family of
equilibria `ε ↦ (P(ε), B(ε))` for the surpluses `s(ε)` and the targets `i(ε)` on `famDom` is
`(priceFam, debtFam)`. -/
theorem family_unique (hPO : 𝔼.PullOut) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hs : ∀ t ω, |shat t ω| ≤ M) {PF BF : ℝ → ℕ → Ω → ℝ}
    (h : ∀ ε ∈ famDom sbar M,
      FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε) (BF ε) (PF ε) (iF ε)) :
    ∀ ε ∈ famDom sbar M,
      PF ε = priceFam 𝔼 β sbar shat Bm1 iF ε ∧ BF ε = debtFam 𝔼 β sbar shat Bm1 iF ε :=
  fun ε hε => fam_unique 𝔼 hPO hβ1 hβ0 hs hε (h ε hε)

/-- Cochrane (2023), §2.4.3, p. 31: the recursion of the family's price level, state by state,
`P_{t+1}(ε) = (1 + i_t(ε)) P_t(ε) PVex_t(ε)/PV_{t+1}(ε)`. -/
theorem priceFam_succ (ε : ℝ) (t : ℕ) (ω : Ω) :
    priceFam 𝔼 β sbar shat Bm1 iF ε (t + 1) ω = (1 + iF ε t ω) *
      priceFam 𝔼 β sbar shat Bm1 iF ε t ω *
        FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω /
          FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) (t + 1) ω := rfl

/-- Cochrane (2023), §2.4.3, p. 31: the family's initial price level `P_0(ε) = B_{−1}/PV_0(ε)`. -/
theorem priceFam_zero (ε : ℝ) (ω : Ω) :
    priceFam 𝔼 β sbar shat Bm1 iF ε 0 ω =
      Bm1 ω / FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) 0 ω := rfl

/-- Cochrane (2023), §2.4.3, p. 31: on `famDom` the family's price level is positive. -/
theorem priceFam_pos (hβ0 : 0 < β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    (hB : ∀ ω, 0 < Bm1 ω) (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω) {ε : ℝ}
    (hε : ε ∈ famDom sbar M) (t : ℕ) (ω : Ω) : 0 < priceFam 𝔼 β sbar shat Bm1 iF ε t ω :=
  FiscalMonetary.pegP_pos hB (hiG ε hε) (pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε)
    (pvEx_surpFam_pos 𝔼 hβ0 hβ1 hs hε) t ω

/-- Cochrane (2023), §2.5, p. 35 (variables as deviations from the steady state): at `ε = 0`,
with `i(0) = 1/β − 1`, the family is the steady state, `P_t = B_{−1}/V` and `B_t = B_{−1}`. -/
theorem fam_steady (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hi0 : ∀ t ω, iF 0 t ω = β⁻¹ - 1) (t : ℕ) :
    priceFam 𝔼 β sbar shat Bm1 iF 0 t = (fun ω => Bm1 ω / ssV β sbar) ∧
      debtFam 𝔼 β sbar shat Bm1 iF 0 t = Bm1 := by
  have hV : ssV β sbar ≠ 0 := mul_ne_zero (inv_ne_zero (by linarith)) hsbar.ne'
  have hpv : ∀ t ω, FiscalMonetary.pv 𝔼 β (surpFam sbar shat 0) t ω = ssV β sbar := by
    intro t ω
    rw [pv_surpFam 𝔼 hβ0.le hβ1 hs]
    ring
  have hpvEx : ∀ t ω, FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat 0) t ω = β * ssV β sbar := by
    intro t ω
    rw [pvEx_surpFam 𝔼 hβ0.le hβ1 hs]
    ring
  have hP : ∀ t, priceFam 𝔼 β sbar shat Bm1 iF 0 t = fun ω => Bm1 ω / ssV β sbar := by
    intro t
    induction t with
    | zero =>
      funext ω
      rw [priceFam_zero, hpv]
    | succ t ih =>
      funext ω
      rw [priceFam_succ, hpv, hpvEx, hi0, ih]
      field_simp
      ring
  refine ⟨hP t, ?_⟩
  funext ω
  change (1 + iF 0 t ω) * priceFam 𝔼 β sbar shat Bm1 iF 0 t ω *
    FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat 0) t ω = Bm1 ω
  rw [hP t, hpvEx, hi0]
  field_simp
  ring

/-! ### Smoothness in the shock size -/

/-- Cochrane (2023), eq. (2.7), p. 22: the present value of the surplus family is a smooth
(affine) function of `ε` in every state. -/
theorem pv_contDiff (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    {n : WithTop ℕ∞} (t : ℕ) (ω : Ω) :
    ContDiff ℝ n (fun ε => FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t ω) := by
  have e : (fun ε => FiscalMonetary.pv 𝔼 β (surpFam sbar shat ε) t ω) =
      fun ε => ssV β sbar + ε * FiscalMonetary.pv 𝔼 β shat t ω :=
    funext fun ε => by rw [pv_surpFam 𝔼 hβ0 hβ1 hs]
  rw [e]
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

/-- Cochrane (2023), eq. (2.15), p. 31: the ex-dividend present value of the surplus family is a
smooth (affine) function of `ε` in every state. -/
theorem pvEx_contDiff (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    {n : WithTop ℕ∞} (t : ℕ) (ω : Ω) :
    ContDiff ℝ n (fun ε => FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω) := by
  have e : (fun ε => FiscalMonetary.pvEx 𝔼 β (surpFam sbar shat ε) t ω) =
      fun ε => β * ssV β sbar + ε * FiscalMonetary.pvEx 𝔼 β shat t ω :=
    funext fun ε => by rw [pvEx_surpFam 𝔼 hβ0 hβ1 hs]
  rw [e]
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

/-- Cochrane (2023), §2.4.3, p. 31: if the rate family is `C^n` in `ε` on `famDom` (any
`n`, including `∞` and analytic), so is the price level of the equilibrium family, in every
state at every date. -/
theorem price_contDiffOn (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    {n : WithTop ℕ∞} (hiC : ∀ t ω, ContDiffOn ℝ n (fun ε => iF ε t ω) (famDom sbar M))
    (t : ℕ) (ω : Ω) :
    ContDiffOn ℝ n (fun ε => priceFam 𝔼 β sbar shat Bm1 iF ε t ω) (famDom sbar M) := by
  induction t with
  | zero =>
    exact contDiffOn_const.div (pv_contDiff 𝔼 hβ0 hβ1 hs 0 ω).contDiffOn
      (fun ε hε => (pv_surpFam_pos 𝔼 hβ0 hβ1 hs hε 0 ω).ne')
  | succ t ih =>
    exact (((contDiffOn_const.add (hiC t ω)).mul ih).mul
      (pvEx_contDiff 𝔼 hβ0 hβ1 hs t ω).contDiffOn).div
      (pv_contDiff 𝔼 hβ0 hβ1 hs (t + 1) ω).contDiffOn
      (fun ε hε => (pv_surpFam_pos 𝔼 hβ0 hβ1 hs hε (t + 1) ω).ne')

/-- Cochrane (2023), eq. (2.15), p. 31: if the rate family is `C^n` on `famDom`, so is the debt
sold along the equilibrium family. -/
theorem debt_contDiffOn (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M)
    {n : WithTop ℕ∞} (hiC : ∀ t ω, ContDiffOn ℝ n (fun ε => iF ε t ω) (famDom sbar M))
    (t : ℕ) (ω : Ω) :
    ContDiffOn ℝ n (fun ε => debtFam 𝔼 β sbar shat Bm1 iF ε t ω) (famDom sbar M) :=
  ((contDiffOn_const.add (hiC t ω)).mul (price_contDiffOn 𝔼 hβ0 hβ1 hs hiC t ω)).mul
    (pvEx_contDiff 𝔼 hβ0 hβ1 hs t ω).contDiffOn

/-- Cochrane (2023), §2.5, p. 35: if the rate family is `C^n` on `famDom` and exceeds `−1`
there, inflation along the equilibrium family is `C^n` on `famDom` in every state at every
date. -/
theorem infl_contDiffOn (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω)
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω) {n : WithTop ℕ∞}
    (hiC : ∀ t ω, ContDiffOn ℝ n (fun ε => iF ε t ω) (famDom sbar M)) (t : ℕ) (ω : Ω) :
    ContDiffOn ℝ n (fun ε => inflFam 𝔼 β sbar shat Bm1 iF ε t ω) (famDom sbar M) := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  cases t with
  | zero =>
    refine ((price_contDiffOn 𝔼 hβ0.le hβ1 hs hiC 0 ω).div_const _).log fun ε hε => ?_
    exact (div_pos (priceFam_pos 𝔼 hβ0 hβ1 hs hB hiG hε 0 ω) (div_pos (hB ω) hV)).ne'
  | succ t =>
    refine ((price_contDiffOn 𝔼 hβ0.le hβ1 hs hiC (t + 1) ω).div
      (price_contDiffOn 𝔼 hβ0.le hβ1 hs hiC t ω)
      (fun ε hε => (priceFam_pos 𝔼 hβ0 hβ1 hs hB hiG hε t ω).ne')).log fun ε hε => ?_
    exact (div_pos (priceFam_pos 𝔼 hβ0 hβ1 hs hB hiG hε (t + 1) ω)
      (priceFam_pos 𝔼 hβ0 hβ1 hs hB hiG hε t ω)).ne'

/-! ### The derivative at the steady state is the linear model -/

/-- Cochrane (2023), eq. (2.17), p. 35: the fiscal shock of the linear model for the family,
`ε_{Σs,t+1} = ΔE_{t+1} ∑ βʲ s̃_{t+1+j}` with surpluses scaled by steady-state debt,
`s̃ = ŝ/V`; zero at date `0`. -/
noncomputable def fiscShock (β sbar : ℝ) (shat : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => LinearFTMP.pvNews 𝔼 β (fun t ω => (ssV β sbar)⁻¹ * shat t ω) t

/-- Cochrane (2023), eq. (2.17), p. 35, at date `0`: the initial inflation of the linear model,
`π̂_0 = −PV_0(ŝ)/V` (all of the date-`0` present value is news relative to the steady state). -/
noncomputable def infl0 (β sbar : ℝ) (shat : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => -((ssV β sbar)⁻¹ * FiscalMonetary.pv 𝔼 β shat 0 ω)

/-- Cochrane (2023), eq. (2.17), p. 35: the news about the present value of `ŝ`, scaled by
steady-state debt, is the fiscal shock `ε_{Σs,t+1}` (bounded `ŝ`, `0 ≤ β < 1`). -/
theorem scaled_innov_pv (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) (t : ℕ)
    (ω : Ω) : (ssV β sbar)⁻¹ * innov 𝔼 t (FiscalMonetary.pv 𝔼 β shat (t + 1)) ω =
      fiscShock 𝔼 β sbar shat (t + 1) ω := by
  change _ = ∑' k, β ^ k * innov 𝔼 t (fun ω => (ssV β sbar)⁻¹ * shat (t + 1 + k) ω) ω
  rw [FiscalMonetary.news_pv_succ, GeneralLinks.innov_epv_eq_pvNews 𝔼 hβ0 hβ1 hs t]
  unfold LinearFTMP.pvNews
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have e : (fun ω => (ssV β sbar)⁻¹ * shat (t + 1 + k) ω) = (ssV β sbar)⁻¹ • shat (t + 1 + k) :=
    rfl
  rw [e, innov_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eq. (2.17), p. 35: the fiscal shock is a shock (known on arrival, zero
forecast). -/
theorem fiscShock_isShock (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hs : ∀ t ω, |shat t ω| ≤ M) :
    LinearFTMP.IsShock 𝔼 (fiscShock 𝔼 β sbar shat) := by
  have hb : ∀ t ω, |(fun t ω => (ssV β sbar)⁻¹ * shat t ω) t ω| ≤ |(ssV β sbar)⁻¹| * M :=
    fun t ω => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hs t ω) (abs_nonneg _)
  have h := LinearFTMP.pvNews_isShock 𝔼 hβ0 hβ1 hb
  exact ⟨fun t => h.1 t, fun t => h.2 t⟩

/-- Cochrane (2023), eq. (2.17), p. 35: the initial inflation `π̂_0` is known at date `0`. -/
theorem infl0_known : 𝔼.E 0 (infl0 𝔼 β sbar shat) = infl0 𝔼 β sbar shat := by
  have e : infl0 𝔼 β sbar shat = (-(ssV β sbar)⁻¹) • FiscalMonetary.pv 𝔼 β shat 0 := by
    funext ω
    simp only [infl0, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, map_smul, FiscalMonetary.pv_adapted 𝔼 β shat 0]

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35, **the derivative of inflation along the family
of exact equilibria**: for `0 < β < 1`, `s̄ > 0`, bounded `ŝ`, positive `B_{−1}`, a rate family
exceeding `−1` on `famDom` whose log gross rate has derivative `î_t` at `ε = 0`, the derivative
of `π_t(ε)` at the steady state `ε = 0` is the solution (2.19) of the linear model,
`π̂_0 = −PV_0(ŝ)/V` and `π̂_{t+1} = î_t − ε_{Σs,t+1}`. -/
theorem infl_hasDerivAt (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω)
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω) {ihat : ℕ → Ω → ℝ}
    (hiD : ∀ t ω, HasDerivAt (fun ε => Real.log (1 + iF ε t ω)) (ihat t ω) 0) (t : ℕ)
    (ω : Ω) : HasDerivAt (fun ε => inflFam 𝔼 β sbar shat Bm1 iF ε t ω)
      (LinearFTMP.pegSol ihat (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat) t ω) 0 := by
  have hV : 0 < ssV β sbar := mul_pos (inv_pos.mpr (by linarith)) hsbar
  have hnhds := famDom_mem_nhds hsbar M
  cases t with
  | zero =>
    set Y := FiscalMonetary.pv 𝔼 β shat 0 ω with hY
    have hev : (fun ε => inflFam 𝔼 β sbar shat Bm1 iF ε 0 ω) =ᶠ[𝓝 0]
        fun ε => Real.log (ssV β sbar) - Real.log (ssV β sbar + ε * Y) := by
      filter_upwards [hnhds] with ε hε
      have h3 := pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε 0 ω
      rw [pv_surpFam 𝔼 hβ0.le hβ1 hs] at h3
      change Real.log (priceFam 𝔼 β sbar shat Bm1 iF ε 0 ω / (Bm1 ω / ssV β sbar)) = _
      rw [priceFam_zero, pv_surpFam 𝔼 hβ0.le hβ1 hs]
      have hB' := (hB ω).ne'
      rw [show Bm1 ω / (ssV β sbar + ε * Y) / (Bm1 ω / ssV β sbar) =
          ssV β sbar / (ssV β sbar + ε * Y) by field_simp,
        Real.log_div hV.ne' h3.ne']
    have hA : HasDerivAt (fun ε : ℝ => ssV β sbar + ε * Y) Y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const Y).const_add (ssV β sbar)
    have hL := (hA.log (by simpa using hV.ne')).const_sub (Real.log (ssV β sbar))
    refine (hL.congr_of_eventuallyEq hev).congr_deriv ?_
    change -(Y / (ssV β sbar + 0 * Y)) = -((ssV β sbar)⁻¹ * Y)
    rw [zero_mul, add_zero, div_eq_inv_mul]
  | succ t =>
    set X := FiscalMonetary.pvEx 𝔼 β shat t ω with hX
    set Y := FiscalMonetary.pv 𝔼 β shat (t + 1) ω with hY
    have hev : (fun ε => inflFam 𝔼 β sbar shat Bm1 iF ε (t + 1) ω) =ᶠ[𝓝 0]
        fun ε => Real.log (1 + iF ε t ω) + Real.log (β * ssV β sbar + ε * X) -
          Real.log (ssV β sbar + ε * Y) := by
      filter_upwards [hnhds] with ε hε
      have hP := priceFam_pos 𝔼 hβ0 hβ1 hs hB hiG hε t ω
      have h1 : 0 < 1 + iF ε t ω := by linarith [hiG ε hε t ω]
      have h2 := pvEx_surpFam_pos 𝔼 hβ0 hβ1 hs hε t ω
      rw [pvEx_surpFam 𝔼 hβ0.le hβ1 hs] at h2
      have h3 := pv_surpFam_pos 𝔼 hβ0.le hβ1 hs hε (t + 1) ω
      rw [pv_surpFam 𝔼 hβ0.le hβ1 hs] at h3
      change Real.log (priceFam 𝔼 β sbar shat Bm1 iF ε (t + 1) ω /
        priceFam 𝔼 β sbar shat Bm1 iF ε t ω) = _
      rw [priceFam_succ, pvEx_surpFam 𝔼 hβ0.le hβ1 hs, pv_surpFam 𝔼 hβ0.le hβ1 hs]
      have hP' := hP.ne'
      rw [show (1 + iF ε t ω) * priceFam 𝔼 β sbar shat Bm1 iF ε t ω *
          (β * ssV β sbar + ε * X) / (ssV β sbar + ε * Y) /
            priceFam 𝔼 β sbar shat Bm1 iF ε t ω =
          (1 + iF ε t ω) * (β * ssV β sbar + ε * X) / (ssV β sbar + ε * Y) by field_simp,
        Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
    have hA : HasDerivAt (fun ε : ℝ => β * ssV β sbar + ε * X) X 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const X).const_add (β * ssV β sbar)
    have hC : HasDerivAt (fun ε : ℝ => ssV β sbar + ε * Y) Y 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const Y).const_add (ssV β sbar)
    have hbV : β * ssV β sbar ≠ 0 := (mul_pos hβ0 hV).ne'
    have hL := HasDerivAt.sub (HasDerivAt.add (hiD t ω) (hA.log (by simpa using hbV)))
      (hC.log (by simpa using hV.ne'))
    refine (hL.congr_of_eventuallyEq hev).congr_deriv ?_
    have hshock := scaled_innov_pv 𝔼 (sbar := sbar) hβ0.le hβ1 hs t ω
    have hXe : X = β * 𝔼.E t (FiscalMonetary.pv 𝔼 β shat (t + 1)) ω := by
      rw [hX, FiscalMonetary.pvEx_eq]
      rfl
    have hin : innov 𝔼 t (FiscalMonetary.pv 𝔼 β shat (t + 1)) ω =
        Y - 𝔼.E t (FiscalMonetary.pv 𝔼 β shat (t + 1)) ω := by
      unfold innov
      rw [FiscalMonetary.pv_adapted 𝔼 β shat (t + 1)]
      rfl
    change ihat t ω + X / (β * ssV β sbar + 0 * X) - Y / (ssV β sbar + 0 * Y) =
      ihat t ω - fiscShock 𝔼 β sbar shat (t + 1) ω
    rw [← hshock, hin, hXe, zero_mul, add_zero, zero_mul, add_zero]
    field_simp
    ring

/-- Cochrane (2023), §2.5, pp. 35–36, (2.16)–(2.19), **the linear model is the derivative of the
family of exact equilibria**: under the hypotheses of `infl_hasDerivAt` with pull-out, an
adapted `î` and positive initial debt known at `0`, the linear model `LinearFTMP.PegModel` with
the rate `î`, the fiscal shock `ε_{Σs}` and `π̂_0 = −PV_0(ŝ)/V` has exactly one adapted
solution, and every adapted solution is the derivative at `ε = 0` of inflation along the
family. -/
theorem fam_linearization (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    (hs : ∀ t ω, |shat t ω| ≤ M) (hB : ∀ ω, 0 < Bm1 ω)
    (hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < iF ε t ω) {ihat : ℕ → Ω → ℝ}
    (hihat : 𝔼.Adapted ihat)
    (hiD : ∀ t ω, HasDerivAt (fun ε => Real.log (1 + iF ε t ω)) (ihat t ω) 0) :
    (∃! π : ℕ → Ω → ℝ, 𝔼.Adapted π ∧ π 0 = infl0 𝔼 β sbar shat ∧
      LinearFTMP.PegModel 𝔼 ihat (fiscShock 𝔼 β sbar shat) π) ∧
    ∀ π : ℕ → Ω → ℝ, 𝔼.Adapted π → π 0 = infl0 𝔼 β sbar shat →
      LinearFTMP.PegModel 𝔼 ihat (fiscShock 𝔼 β sbar shat) π →
        ∀ t ω, HasDerivAt (fun ε => inflFam 𝔼 β sbar shat Bm1 iF ε t ω) (π t ω) 0 := by
  have hk := infl0_known 𝔼 (β := β) (sbar := sbar) (shat := shat)
  have hex := LinearFTMP.peg_existsUnique 𝔼 hk hihat
    (fiscShock_isShock 𝔼 (sbar := sbar) hβ0.le hβ1 hs)
  refine ⟨hex, fun π hπ hπ0 hm t ω => ?_⟩
  obtain ⟨π', hπ', hu⟩ := hex
  have e1 := hu π ⟨hπ, hπ0, hm⟩
  have e2 := hu (LinearFTMP.pegSol ihat (fiscShock 𝔼 β sbar shat) (infl0 𝔼 β sbar shat))
    ⟨LinearFTMP.pegSol_adapted 𝔼 hk hihat
      (fiscShock_isShock 𝔼 (sbar := sbar) hβ0.le hβ1 hs), rfl,
      (LinearFTMP.pegModel_iff 𝔼 (LinearFTMP.pegSol_adapted 𝔼 hk hihat
        (fiscShock_isShock 𝔼 (sbar := sbar) hβ0.le hβ1 hs)) hihat
        (fiscShock_isShock 𝔼 (sbar := sbar) hβ0.le hβ1 hs)).mpr fun _ => rfl⟩
  rw [e1, ← e2]
  exact infl_hasDerivAt 𝔼 hβ0 hβ1 hsbar hs hB hiG hiD t ω

/-! ### The canonical rate family `1 + i_t(ε) = β⁻¹ exp(ε î_t)` -/

/-- Cochrane (2023), eq. (2.16), p. 35 (`i_t` as the log deviation of the gross rate from
`r = −log β`): the rate family `1 + i_t(ε) = β⁻¹ exp(ε î_t)`. -/
noncomputable def rateExp (β : ℝ) (ihat : ℕ → Ω → ℝ) (ε : ℝ) : ℕ → Ω → ℝ :=
  fun t ω => β⁻¹ * Real.exp (ε * ihat t ω) - 1

omit 𝔼 in
/-- Cochrane (2023), eq. (2.16), p. 35: the canonical rate family exceeds `−1` (`β > 0`). -/
theorem rateExp_gt (hβ0 : 0 < β) (ihat : ℕ → Ω → ℝ) (ε : ℝ) (t : ℕ) (ω : Ω) :
    -1 < rateExp β ihat ε t ω := by
  simp only [rateExp]
  have := mul_pos (inv_pos.mpr hβ0) (Real.exp_pos (ε * ihat t ω))
  linarith

omit 𝔼 in
/-- Cochrane (2023), eq. (2.16), p. 35: at `ε = 0` the canonical rate is the steady-state rate
`1/β − 1`. -/
theorem rateExp_zero (ihat : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : rateExp β ihat 0 t ω = β⁻¹ - 1 := by
  simp [rateExp]

/-- Cochrane (2023), eq. (2.16), p. 35: with `FunctionsKnown`, the canonical rate family is
adapted when `î` is. -/
theorem rateExp_adapted (hFK : FunctionsKnown 𝔼) {ihat : ℕ → Ω → ℝ} (hihat : 𝔼.Adapted ihat)
    (ε : ℝ) : 𝔼.Adapted (rateExp β ihat ε) :=
  fun t => hFK t (ihat t) (fun x => β⁻¹ * Real.exp (ε * x) - 1) (hihat t)

omit 𝔼 in
/-- Cochrane (2023), eq. (2.16), p. 35: `log(1 + i_t(ε)) = r + ε î_t` exactly, so its derivative
at `ε = 0` is `î_t` (`β > 0`). -/
theorem rateExp_log_hasDerivAt (hβ0 : 0 < β) (ihat : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => Real.log (1 + rateExp β ihat ε t ω)) (ihat t ω) 0 := by
  have e : (fun ε => Real.log (1 + rateExp β ihat ε t ω)) =
      fun ε => Real.log β⁻¹ + ε * ihat t ω := by
    funext ε
    simp only [rateExp, add_sub_cancel]
    rw [Real.log_mul (inv_pos.mpr hβ0).ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (ihat t ω)).const_add (Real.log β⁻¹)

omit 𝔼 in
/-- Cochrane (2023), eq. (2.16), p. 35: the canonical rate family is `C^n` in `ε` for every
`n` (including `∞` and analytic). -/
theorem rateExp_contDiff (ihat : ℕ → Ω → ℝ) {n : WithTop ℕ∞} (t : ℕ) (ω : Ω) :
    ContDiff ℝ n (fun ε => rateExp β ihat ε t ω) :=
  (contDiff_const.mul ((contDiff_id.mul contDiff_const).exp)).sub contDiff_const

/-- Cochrane (2023), §§2.4–2.5, pp. 31–36, **the family of exact equilibria under the canonical
target**, all in one statement. With pull-out, `FunctionsKnown`, `0 < β < 1`, `s̄ > 0`, bounded
adapted `ŝ`, adapted `î` and positive initial debt known at `0`, on the open neighbourhood
`famDom` of `ε = 0`:
* for each `ε` the family member is an equilibrium, and the only one;
* at `ε = 0` it is the steady state;
* price level, debt and inflation are `C^n` in `ε` for every `n`;
* the linear model (2.16)–(2.19) with `π̂_0 = −PV_0(ŝ)/V` has exactly one adapted solution, and
  it is the derivative at `ε = 0` of inflation along the family. -/
theorem exp_family_linearization (hPO : 𝔼.PullOut) (hFK : FunctionsKnown 𝔼) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hsbar : 0 < sbar) (hs : ∀ t ω, |shat t ω| ≤ M)
    (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω) {ihat : ℕ → Ω → ℝ}
    (hihat : 𝔼.Adapted ihat) :
    (0 : ℝ) ∈ famDom sbar M ∧ IsOpen (famDom sbar M) ∧
    (∀ ε ∈ famDom sbar M, FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε)
      (debtFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε)
      (priceFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε) (rateExp β ihat ε)) ∧
    (∀ ε ∈ famDom sbar M, ∀ B P : ℕ → Ω → ℝ,
      FiscalMonetary.Equilibrium 𝔼 β Bm1 (surpFam sbar shat ε) B P (rateExp β ihat ε) →
        P = priceFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε ∧
          B = debtFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε) ∧
    (∀ t, priceFam 𝔼 β sbar shat Bm1 (rateExp β ihat) 0 t = (fun ω => Bm1 ω / ssV β sbar) ∧
      debtFam 𝔼 β sbar shat Bm1 (rateExp β ihat) 0 t = Bm1) ∧
    (∀ (n : WithTop ℕ∞) t ω,
      ContDiffOn ℝ n (fun ε => priceFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => debtFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε t ω)
        (famDom sbar M) ∧
      ContDiffOn ℝ n (fun ε => inflFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε t ω)
        (famDom sbar M)) ∧
    (∃! π : ℕ → Ω → ℝ, 𝔼.Adapted π ∧ π 0 = infl0 𝔼 β sbar shat ∧
      LinearFTMP.PegModel 𝔼 ihat (fiscShock 𝔼 β sbar shat) π) ∧
    ∀ π : ℕ → Ω → ℝ, 𝔼.Adapted π → π 0 = infl0 𝔼 β sbar shat →
      LinearFTMP.PegModel 𝔼 ihat (fiscShock 𝔼 β sbar shat) π →
        ∀ t ω, HasDerivAt (fun ε => inflFam 𝔼 β sbar shat Bm1 (rateExp β ihat) ε t ω)
          (π t ω) 0 := by
  have hiG : ∀ ε ∈ famDom sbar M, ∀ t ω, -1 < rateExp β ihat ε t ω :=
    fun ε _ t ω => rateExp_gt hβ0 ihat ε t ω
  have hiC : ∀ (n : WithTop ℕ∞) t ω,
      ContDiffOn ℝ n (fun ε => rateExp β ihat ε t ω) (famDom sbar M) :=
    fun n t ω => (rateExp_contDiff ihat t ω).contDiffOn
  obtain ⟨hlin1, hlin2⟩ := fam_linearization 𝔼 (Bm1 := Bm1) hβ0 hβ1 hsbar hs hB hiG hihat
    (rateExp_log_hasDerivAt hβ0 ihat)
  refine ⟨zero_mem_famDom hsbar M, famDom_isOpen sbar M, fun ε hε => ?_, fun ε hε B P h => ?_,
    fun t => ?_, fun n t ω => ⟨?_, ?_, ?_⟩, hlin1, hlin2⟩
  · exact fam_equilibrium 𝔼 hPO hβ0 hβ1 hs hBm1 hB
      (fun ε _ => rateExp_adapted 𝔼 hFK hihat ε) hiG hε
  · exact fam_unique 𝔼 hPO hβ1 hβ0.le hs hε h
  · exact fam_steady 𝔼 hβ0 hβ1 hsbar hs (rateExp_zero ihat) t
  · exact price_contDiffOn 𝔼 hβ0.le hβ1 hs (hiC n) t ω
  · exact debt_contDiffOn 𝔼 hβ0.le hβ1 hs (hiC n) t ω
  · exact infl_contDiffOn 𝔼 hβ0 hβ1 hsbar hs hB hiG (hiC n) t ω

/-- Cochrane (2023), §§2.4–2.5, pp. 31–36, on every finite event tree (genuine uncertainty):
the family of exact equilibria under the canonical target exists on a neighbourhood of `ε = 0`,
is unique, is the steady state at `0`, is smooth, and its derivative at `0` is the unique
adapted solution of the linear model (`exp_family_linearization` with the tree's pull-out and
`FunctionsKnown`). -/
theorem tree_family_linearization {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') (hβ0 : 0 < β) (hβ1 : β < 1) (hsbar : 0 < sbar)
    {shat' : ℕ → Ω' → ℝ} (hs : ∀ t ω, |shat' t ω| ≤ M) {Bm1' : Ω' → ℝ}
    (hBm1 : T.toExpectationSystem.E 0 Bm1' = Bm1') (hB : ∀ ω, 0 < Bm1' ω)
    {ihat : ℕ → Ω' → ℝ} (hihat : T.toExpectationSystem.Adapted ihat) (ε : ℝ)
    (hε : ε ∈ famDom sbar M) :
    FiscalMonetary.Equilibrium T.toExpectationSystem β Bm1' (surpFam sbar shat' ε)
      (debtFam T.toExpectationSystem β sbar shat' Bm1' (rateExp β ihat) ε)
      (priceFam T.toExpectationSystem β sbar shat' Bm1' (rateExp β ihat) ε)
      (rateExp β ihat ε) ∧
    ∀ π : ℕ → Ω' → ℝ, T.toExpectationSystem.Adapted π →
      π 0 = infl0 T.toExpectationSystem β sbar shat' →
      LinearFTMP.PegModel T.toExpectationSystem ihat
        (fiscShock T.toExpectationSystem β sbar shat') π →
        ∀ t ω, HasDerivAt (fun ε =>
          inflFam T.toExpectationSystem β sbar shat' Bm1' (rateExp β ihat) ε t ω) (π t ω) 0 := by
  have h := exp_family_linearization T.toExpectationSystem
    (ExpectationsFiniteTree.finiteTree_pullOut T) (finiteTree_functionsKnown T) hβ0 hβ1 hsbar hs
    hBm1 hB hihat
  exact ⟨h.2.2.1 ε hε, h.2.2.2.2.2.2.2⟩

end Cochrane.IntertemporalModel.TidyR5Family
