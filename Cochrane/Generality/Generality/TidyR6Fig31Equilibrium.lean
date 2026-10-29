/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR6InnovGrowth

/-!
# Figure 3.1 and the announcement results as equilibria of a full model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.5.3, pp. 68–70
((3.27)–(3.28) and Figure 3.1), with the bond-price identity of Online Appendix A1.3,
pp. 561–564.

`LogLinearIdentities` proved Figure 3.1 and the announcement results on sequences of inflation
innovations that satisfy (3.28) (`LogLinearIdentities.fig31_jump`,
`LogLinearIdentities.announcement_jump`). Here they are properties of the equilibria of a full
model. The model, on an arbitrary `ExpectationSystem`, with `0 < ρ < 1` and `|ω̂| < 1`:

* exogenous: the nominal interest rate `i` set by the central bank and the scaled surplus `s̃`,
  adapted and bounded; no growth (`g = 0`);
* endogenous: the log real value of debt `v`, the log price of the geometric bond portfolio
  `q`, its return `r^n` and inflation `π`, adapted and bounded;
* equations: the bond-return identity (1.24) `r^n_{t+1} = ω̂q_{t+1} − q_t`; the expectations
  hypothesis `E_t r^n_{t+1} = i_t`; the Fisher equation with a constant real rate
  `E_t π_{t+1} = i_t` (p. 69); and the flow (3.17) with `g = 0`.

We prove existence (`exists_eqm`) and uniqueness (`unique_eqm`) of the equilibrium: `q` is the
forward sum of expected rates and `v` the present value of surpluses (`eqm_q_solves`,
`eqm_v_solves`). In every equilibrium expected real returns are constant (`eqm_const_return`),
expected inflation innovations equal rate innovations (`innov_infl_eq_innov_i`), and the
weighted inflation identity (3.23) holds (`eqm_weighted`). Hence, as equilibrium statements:
Figure 3.1 (`fig31_equilibrium`, `fig31_equilibrium_value`, `fig31_equilibrium_path`), the
announcement result (`announcement_equilibrium`) and the expected rise with no jump
(`expected_rise_equilibrium`). The hypotheses are met in a genuinely stochastic economy: on the
coin-flip tree a rate rise announced at date 1 by the first flip produces exactly the Figure 3.1
response (`CoinEconomy.fig31_coin_economy`).
-/

namespace Cochrane.Generality.TidyR6Fig31Equilibrium

open Filter Topology
open Cochrane.Generality.LogLinearIdentities

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)
variable (ρ ωh : ℝ) (i sT v q rn infl : ℕ → Ω → ℝ)

/-- Cochrane (2023), §3.5.3, pp. 68–70, and A1.3: an equilibrium of the linear fiscal model with
long-term debt and an interest-rate target `i`: adapted bounded `v`, `q`, `r^n`, `π` satisfying
the bond-return identity (1.24), the expectations hypothesis `E_tr^n_{t+1} = i_t`, the Fisher
equation `E_tπ_{t+1} = i_t` (constant real rate) and the flow (3.17) with no growth. -/
structure Equilibrium where
  v_adapted : 𝔼.Adapted v
  q_adapted : 𝔼.Adapted q
  rn_adapted : 𝔼.Adapted rn
  infl_adapted : 𝔼.Adapted infl
  v_bdd : BoundedProc v
  q_bdd : BoundedProc q
  rn_bdd : BoundedProc rn
  infl_bdd : BoundedProc infl
  bond : BondRet ωh q rn
  eh : ∀ t, 𝔼.E t (rn (t + 1)) = i t
  fisher : ∀ t, 𝔼.E t (infl (t + 1)) = i t
  flow : Flow317 ρ v rn infl (fun _ _ => 0) sT

variable {𝔼 ρ ωh i sT v q rn infl}

/-- Cochrane (2023), p. 66 and p. 69: in equilibrium expected real returns are constant,
`E_t(r^n_{t+1} − π_{t+1}) = 0`. -/
theorem eqm_const_return (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (n : ℕ) :
    𝔼.E n (rn (n + 1) - infl (n + 1)) = 0 := by
  rw [map_sub, hE.eh n, hE.fisher n, sub_self]

/-- Cochrane (2023), §3.5, pp. 63–65: every equilibrium is a bounded linear economy
(`LogLinearIdentities.LinearEconomy`) with `g = 0`. -/
theorem eqm_linearEconomy (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT) :
    LinearEconomy 𝔼 ρ v rn infl (fun _ _ => 0) sT where
  flow := hE.flow
  v_adapted := hE.v_adapted
  rn_adapted := hE.rn_adapted
  infl_adapted := hE.infl_adapted
  g_adapted := fun t => 𝔼.const t 0
  s_adapted := hsa
  rho_pos := hρ0
  rho_lt_one := hρ1
  v_bdd := hE.v_bdd
  rn_bdd := hE.rn_bdd
  infl_bdd := hE.infl_bdd
  g_bdd := ⟨0, fun _ _ => by simp⟩
  s_bdd := hsb

/-- Cochrane (2023), A1 p. 564: in equilibrium the log bond price solves
`q_t = ω̂E_tq_{t+1} − i_t`. -/
theorem eqm_q_solves (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) :
    ForwardSolution.Solves 𝔼 ωh (fun t => -i t) q := by
  intro t
  have h := (EH_bond hE.bond hE.q_adapted t).mp (hE.eh t)
  change q t = ωh • 𝔼.E t (q (t + 1)) + -i t
  rw [← h]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), (3.19), p. 64: in equilibrium the value of debt solves
`v_t = ρE_tv_{t+1} + E_t s̃_{t+1}` (expected returns are constant). -/
theorem eqm_v_solves (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) :
    ForwardSolution.Solves 𝔼 ρ (fun t => 𝔼.E t (sT (t + 1))) v := by
  intro t
  have hf : ρ • v (t + 1) = v t + (rn (t + 1) - infl (t + 1)) - sT (t + 1) := by
    funext ω
    have := hE.flow t ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply]
    linarith
  have h := congrArg (𝔼.E t) hf
  rw [map_smul, map_sub, map_add, hE.v_adapted t, eqm_const_return hE t, add_zero] at h
  rw [h]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-! ### Existence and uniqueness -/

variable (𝔼 ρ ωh i sT)

/-- Cochrane (2023), A1 p. 564: the equilibrium log bond price, the forward sum
`q_t = −∑_k ω̂ᵏE_t i_{t+k}`. -/
noncomputable def eqQ : ℕ → Ω → ℝ := 𝔼.forwardSeries ωh (fun t => -i t)

/-- Cochrane (2023), (3.19), p. 64: the equilibrium value of debt, the present value
`v_t = ∑_k ρᵏE_t s̃_{t+1+k}`. -/
noncomputable def eqV : ℕ → Ω → ℝ := 𝔼.forwardSeries ρ (fun t => 𝔼.E t (sT (t + 1)))

/-- Cochrane (2023), A1 (1.24): the equilibrium bond return `r^n_{n} = ω̂q_n − q_{n−1}` (`n ≥ 1`;
the pre-sample value is `0`). -/
noncomputable def eqRn : ℕ → Ω → ℝ :=
  fun n => if n = 0 then 0 else ωh • eqQ 𝔼 ωh i n - eqQ 𝔼 ωh i (n - 1)

/-- Cochrane (2023), (3.17), p. 63: the equilibrium inflation
`π_n = v_{n−1} + r^n_n − s̃_n − ρv_n` (`n ≥ 1`; the pre-sample value is `0`). -/
noncomputable def eqInfl : ℕ → Ω → ℝ :=
  fun n => if n = 0 then 0 else
    eqV 𝔼 ρ sT (n - 1) + eqRn 𝔼 ωh i n - sT n - ρ • eqV 𝔼 ρ sT n

variable {𝔼 ρ ωh i sT}

/-- Cochrane (2023), §3.5.3 and A1.3: **existence.** For bounded adapted `i` and `s̃`,
`0 < ρ < 1` and `|ω̂| < 1`, the processes `eqV`, `eqQ`, `eqRn`, `eqInfl` form an equilibrium. -/
theorem exists_eqm (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω : |ωh| < 1) (hia : 𝔼.Adapted i)
    (hib : BoundedProc i) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT) :
    Equilibrium 𝔼 ρ ωh i sT (eqV 𝔼 ρ sT) (eqQ 𝔼 ωh i) (eqRn 𝔼 ωh i) (eqInfl 𝔼 ρ ωh i sT) := by
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Ms, hMs⟩ := hsb
  have hρ : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hni : ∀ t ω, |(fun t => -i t) t ω| ≤ Mi := fun t ω => by
    simpa using hMi t ω
  have hnia : 𝔼.Adapted fun t => -i t := fun t => by rw [map_neg, hia t]
  have hes : ∀ t ω, |(fun t => 𝔼.E t (sT (t + 1))) t ω| ≤ Ms := fun t ω =>
    𝔼.abs_E_le (hMs (t + 1)) t ω
  have hesa : 𝔼.Adapted fun t => 𝔼.E t (sT (t + 1)) := fun t => 𝔼.E_E_self t _
  have hqs := ForwardSolution.forwardSeries_solves_abs 𝔼 hω hni hnia
  have hqa := ForwardSolution.forwardSeries_adapted_abs 𝔼 hω hni
  have hqb := ForwardSolution.forwardSeries_bounded_abs 𝔼 hω hni
  have hvs := ForwardSolution.forwardSeries_solves_abs 𝔼 hρ hes hesa
  have hva := ForwardSolution.forwardSeries_adapted_abs 𝔼 hρ hes
  have hvb := ForwardSolution.forwardSeries_bounded_abs 𝔼 hρ hes
  change ForwardSolution.Solves 𝔼 ωh (fun t => -i t) (eqQ 𝔼 ωh i) at hqs
  change 𝔼.Adapted (eqQ 𝔼 ωh i) at hqa
  change BoundedProc (eqQ 𝔼 ωh i) at hqb
  change ForwardSolution.Solves 𝔼 ρ (fun t => 𝔼.E t (sT (t + 1))) (eqV 𝔼 ρ sT) at hvs
  change 𝔼.Adapted (eqV 𝔼 ρ sT) at hva
  change BoundedProc (eqV 𝔼 ρ sT) at hvb
  have hrn : ∀ t, eqRn 𝔼 ωh i (t + 1) = ωh • eqQ 𝔼 ωh i (t + 1) - eqQ 𝔼 ωh i t := fun t => by
    simp [eqRn]
  have hpi : ∀ t, eqInfl 𝔼 ρ ωh i sT (t + 1) = eqV 𝔼 ρ sT t + eqRn 𝔼 ωh i (t + 1) -
      sT (t + 1) - ρ • eqV 𝔼 ρ sT (t + 1) := fun t => by
    simp [eqInfl]
  have hEH : ∀ t, 𝔼.E t (eqRn 𝔼 ωh i (t + 1)) = i t := by
    intro t
    have h := hqs t
    rw [hrn, map_sub, map_smul, hqa t]
    have : eqQ 𝔼 ωh i t = ωh • 𝔼.E t (eqQ 𝔼 ωh i (t + 1)) - i t := by
      rw [h]
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hrna : 𝔼.Adapted (eqRn 𝔼 ωh i) := by
    intro n
    rcases n with _ | t
    · simp only [eqRn, ↓reduceIte]
      exact map_zero _
    · rw [hrn, map_sub, map_smul, hqa (t + 1), ForwardSolution.E_of_known 𝔼 (Nat.le_succ t)
        (hqa t)]
  obtain ⟨Mq, hMq⟩ := hqb
  obtain ⟨Mv, hMv⟩ := hvb
  have hrnb : BoundedProc (eqRn 𝔼 ωh i) := by
    refine ⟨|ωh| * Mq + Mq, fun n ω => ?_⟩
    rcases n with _ | t
    · simp only [eqRn, ↓reduceIte, Pi.zero_apply, abs_zero]
      have h0 : 0 ≤ Mq := (abs_nonneg _).trans (hMq 0 ω)
      positivity
    · rw [hrn, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans (add_le_add ?_ (hMq t ω))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMq (t + 1) ω) (abs_nonneg _)
  refine
    { v_adapted := hva
      q_adapted := hqa
      rn_adapted := hrna
      infl_adapted := fun n => ?_
      v_bdd := ⟨Mv, hMv⟩
      q_bdd := ⟨Mq, hMq⟩
      rn_bdd := hrnb
      infl_bdd := ?_
      bond := fun t ω => by rw [hrn]; rfl
      eh := hEH
      fisher := fun t => ?_
      flow := fun t ω => ?_ }
  · rcases n with _ | t
    · simp only [eqInfl, ↓reduceIte]
      exact map_zero _
    · rw [hpi, map_sub, map_sub, map_add, map_smul, hva (t + 1), hrna (t + 1), hsa (t + 1),
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hva t)]
  · obtain ⟨Mr, hMr⟩ := hrnb
    refine ⟨Mv + Mr + Ms + ρ * Mv, fun n ω => ?_⟩
    have hv0 : 0 ≤ Mv := (abs_nonneg _).trans (hMv 0 ω)
    have hr0 : 0 ≤ Mr := (abs_nonneg _).trans (hMr 0 ω)
    have hs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs 0 ω)
    rcases n with _ | t
    · simp only [eqInfl, ↓reduceIte, Pi.zero_apply, abs_zero]
      positivity
    · rw [hpi]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := hMv t ω
      have h2 := hMr (t + 1) ω
      have h3 := hMs (t + 1) ω
      have h4 : |ρ * eqV 𝔼 ρ sT (t + 1) ω| ≤ ρ * Mv := by
        rw [abs_mul, abs_of_pos hρ0]
        exact mul_le_mul_of_nonneg_left (hMv (t + 1) ω) hρ0.le
      calc |eqV 𝔼 ρ sT t ω + eqRn 𝔼 ωh i (t + 1) ω - sT (t + 1) ω -
            ρ * eqV 𝔼 ρ sT (t + 1) ω|
          ≤ |eqV 𝔼 ρ sT t ω| + |eqRn 𝔼 ωh i (t + 1) ω| + |sT (t + 1) ω| +
            |ρ * eqV 𝔼 ρ sT (t + 1) ω| := by
            have e1 := abs_sub (eqV 𝔼 ρ sT t ω + eqRn 𝔼 ωh i (t + 1) ω - sT (t + 1) ω)
              (ρ * eqV 𝔼 ρ sT (t + 1) ω)
            have e2 := abs_sub (eqV 𝔼 ρ sT t ω + eqRn 𝔼 ωh i (t + 1) ω) (sT (t + 1) ω)
            have e3 := abs_add_le (eqV 𝔼 ρ sT t ω) (eqRn 𝔼 ωh i (t + 1) ω)
            linarith
        _ ≤ Mv + Mr + Ms + ρ * Mv := by linarith
  · have h := hvs t
    rw [hpi, map_sub, map_sub, map_add, map_smul, hva t, hEH t]
    have hv : eqV 𝔼 ρ sT t = ρ • 𝔼.E t (eqV 𝔼 ρ sT (t + 1)) + 𝔼.E t (sT (t + 1)) := h
    rw [hv]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hpi]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), §3.5.3 and A1.3: **uniqueness.** Any two equilibria (with the same bounded
adapted `i`, `s̃`, `0 < ρ < 1`, `|ω̂| < 1`) have the same value of debt and bond price at every
date, and the same bond returns and inflation at every date `t + 1 ≥ 1` (the pre-sample date-0
return and inflation do not enter any equation). -/
theorem unique_eqm (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω : |ωh| < 1) (hia : 𝔼.Adapted i)
    (hib : BoundedProc i) (hsb : BoundedProc sT)
    {v' q' rn' infl' : ℕ → Ω → ℝ} (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl)
    (hE' : Equilibrium 𝔼 ρ ωh i sT v' q' rn' infl') :
    v = v' ∧ q = q' ∧ (∀ t, rn (t + 1) = rn' (t + 1)) ∧ ∀ t, infl (t + 1) = infl' (t + 1) := by
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Ms, hMs⟩ := hsb
  have hρ : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have hni : ∀ t ω, |(fun t => -i t) t ω| ≤ Mi := fun t ω => by simpa using hMi t ω
  have hnia : 𝔼.Adapted fun t => -i t := fun t => by rw [map_neg, hia t]
  have hes : ∀ t ω, |(fun t => 𝔼.E t (sT (t + 1))) t ω| ≤ Ms := fun t ω =>
    𝔼.abs_E_le (hMs (t + 1)) t ω
  have hesa : 𝔼.Adapted fun t => 𝔼.E t (sT (t + 1)) := fun t => 𝔼.E_E_self t _
  have hq : q = q' := by
    rw [ForwardSolution.eq_forwardSeries_abs 𝔼 hω hni hnia (eqm_q_solves hE) hE.q_bdd,
      ForwardSolution.eq_forwardSeries_abs 𝔼 hω hni hnia (eqm_q_solves hE') hE'.q_bdd]
  have hv : v = v' := by
    rw [ForwardSolution.eq_forwardSeries_abs 𝔼 hρ hes hesa (eqm_v_solves hE) hE.v_bdd,
      ForwardSolution.eq_forwardSeries_abs 𝔼 hρ hes hesa (eqm_v_solves hE') hE'.v_bdd]
  have hr : ∀ t, rn (t + 1) = rn' (t + 1) := fun t => by
    funext ω
    rw [hE.bond t ω, hE'.bond t ω, hq]
  refine ⟨hv, hq, hr, fun t => ?_⟩
  funext ω
  have h1 := hE.flow t ω
  have h2 := hE'.flow t ω
  rw [hv, hr t] at h1
  linarith

/-! ### Responses in equilibrium -/

/-- Cochrane (2023), p. 69 ("`E_tπ_{t+1} = i_t`"): in equilibrium the news about inflation two or
more periods ahead is the news about the interest rate one period earlier,
`ΔE_{t+1}π_{t+2+j} = ΔE_{t+1}i_{t+1+j}`. -/
theorem innov_infl_eq_innov_i (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (t j : ℕ) :
    innov 𝔼 t (infl (t + j + 2)) = innov 𝔼 t (i (t + j + 1)) := by
  have h1 : 𝔼.E (t + 1) (infl (t + j + 2)) = 𝔼.E (t + 1) (i (t + j + 1)) := by
    rw [← 𝔼.tower (show t + 1 ≤ t + j + 1 by omega), hE.fisher (t + j + 1)]
  have h0 : 𝔼.E t (infl (t + j + 2)) = 𝔼.E t (i (t + j + 1)) := by
    rw [← 𝔼.tower (show t ≤ t + j + 1 by omega), hE.fisher (t + j + 1)]
  simp only [innov, LinearMap.sub_apply, h1, h0]

/-- Cochrane (2023), (3.23), p. 67, in equilibrium: `∑_{j≥0} ω̂^jΔE_{t+1}π_{t+1+j}
= −∑_{j≥0} ρ^jΔE_{t+1}s̃_{t+1+j}`, as a convergent sum. -/
theorem eqm_weighted (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hω : |ωh| < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT) (t : ℕ) (ω : Ω) :
    ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (sT (t + j + 1)) ω :=
  special_constant_long (eqm_linearEconomy hE hρ0 hρ1 hsa hsb) hE.bond
    ⟨hE.q_adapted, hE.q_bdd, hω⟩ (fun _ _ => rfl) (eqm_const_return hE) t ω

/-- Cochrane (2023), (3.28), p. 69, in equilibrium: the inflation innovations
`x_j = ΔE_{t+1}π_{t+1+j}` form a summable sequence, and with no surplus news
`∑_j ω̂^jx_j = 0`. -/
theorem eqm_disinflation (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hω : |ωh| < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT) (t : ℕ) (ω : Ω)
    (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0) :
    Summable (fun j => ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω) ∧
      ∑' j, ωh ^ j * innov 𝔼 t (infl (t + j + 1)) ω = 0 := by
  obtain ⟨M, hM⟩ := hE.infl_bdd
  refine ⟨summable_innov 𝔼 (summable_geometric_of_abs_lt_one hω) hM (fun j => t + j + 1) t ω,
    ?_⟩
  rw [eqm_weighted hE hρ0 hρ1 hω hsa hsb t ω]
  simp [hs]

/-- Cochrane (2023), §3.5.3, p. 69 and **Figure 3.1**, as an equilibrium statement: if at date
`t + 1` (in state `ω`) the news is an unexpected permanent rise of the interest rate by one,
`ΔE_{t+1}i_{t+1+j} = 1` for all `j ≥ 0`, with no surplus news, then in the (unique) equilibrium
inflation jumps by `ΔE_{t+1}π_{t+1} = −ω̂/(1 − ω̂)` on impact and is then one higher,
`ΔE_{t+1}π_{t+2+j} = 1`. -/
theorem fig31_equilibrium (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hω0 : 0 ≤ ωh) (hω1 : ωh < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT)
    (t : ℕ) (ω : Ω) (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0)
    (hi : ∀ j, innov 𝔼 t (i (t + j + 1)) ω = 1) :
    innov 𝔼 t (infl (t + 1)) ω = -(ωh / (1 - ωh)) ∧
      ∀ j, innov 𝔼 t (infl (t + j + 2)) ω = 1 := by
  have hω : |ωh| < 1 := by rw [abs_of_nonneg hω0]; exact hω1
  have hx : ∀ j, (fun j => innov 𝔼 t (infl (t + j + 1)) ω) (j + 1) = 1 := fun j => by
    simp only [show t + (j + 1) + 1 = t + j + 2 by omega, innov_infl_eq_innov_i hE, hi]
  obtain ⟨hsum, h0⟩ := eqm_disinflation hE hρ0 hρ1 hω hsa hsb t ω hs
  refine ⟨?_, fun j => by simpa [show t + (j + 1) + 1 = t + j + 2 by omega] using hx j⟩
  simpa using fig31_jump hω0 hω1 hx hsum h0

/-- Cochrane (2023), Figure 3.1, p. 70: at the figure's `ω = 0.8` the equilibrium impact response
is `−4` (percent). -/
theorem fig31_equilibrium_value (hE : Equilibrium 𝔼 ρ (0.8 : ℝ) i sT v q rn infl) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT) (t : ℕ) (ω : Ω)
    (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0)
    (hi : ∀ j, innov 𝔼 t (i (t + j + 1)) ω = 1) :
    innov 𝔼 t (infl (t + 1)) ω = -4 := by
  rw [(fig31_equilibrium hE hρ0 hρ1 (by norm_num) (by norm_num) hsa hsb t ω hs hi).1]
  norm_num

/-- Cochrane (2023), Figure 3.1, p. 70, in equilibrium: the revision of the log price-level path,
`∑_{k≤n} ΔE_{t+1}π_{t+1+k}`, is `−ω̂/(1 − ω̂)` on impact and then rises by one per period. -/
theorem fig31_equilibrium_path (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hω0 : 0 ≤ ωh) (hω1 : ωh < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT)
    (t : ℕ) (ω : Ω) (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0)
    (hi : ∀ j, innov 𝔼 t (i (t + j + 1)) ω = 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), innov 𝔼 t (infl (t + k + 1)) ω = -(ωh / (1 - ωh)) + n := by
  obtain ⟨h0, h1⟩ := fig31_equilibrium hE hρ0 hρ1 hω0 hω1 hsa hsb t ω hs hi
  exact fig31_path (x := fun k => innov 𝔼 t (infl (t + k + 1)) ω) (by simpa using h0)
    (fun j => by simpa [show t + (j + 1) + 1 = t + j + 2 by omega] using h1 j) n

/-- Cochrane (2023), pp. 69–70 ("announced `k` periods ahead"), as an equilibrium statement: if
at date `t + 1` the interest rate is announced to rise by one from date `t + k` on
(`ΔE_{t+1}i_{t+j} = 0` for `1 ≤ j < k`, `= 1` for `j ≥ k`), with no surplus news, then on
announcement inflation jumps by `ΔE_{t+1}π_{t+1} = −ω̂ᵏ/(1 − ω̂)`. -/
theorem announcement_equilibrium (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hω0 : 0 ≤ ωh) (hω1 : ωh < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT)
    (t : ℕ) (ω : Ω) (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0) {k : ℕ} (hk : 1 ≤ k)
    (hi : ∀ j, 1 ≤ j → innov 𝔼 t (i (t + j)) ω = if j < k then 0 else 1) :
    innov 𝔼 t (infl (t + 1)) ω = -(ωh ^ k / (1 - ωh)) := by
  have hω : |ωh| < 1 := by rw [abs_of_nonneg hω0]; exact hω1
  obtain ⟨hsum, h0⟩ := eqm_disinflation hE hρ0 hρ1 hω hsa hsb t ω hs
  have hx : ∀ j, 1 ≤ j → (fun j => innov 𝔼 t (infl (t + j + 1)) ω) j =
      if j < k then 0 else 1 := by
    intro j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp only [show t + (m + 1) + 1 = t + m + 2 by omega, innov_infl_eq_innov_i hE]
    rw [show t + m + 1 = t + (m + 1) by omega]
    exact hi (m + 1) hj
  simpa using announcement_jump hω0 hω1 hk hx hsum h0

/-- Cochrane (2023), p. 70 ("If the interest-rate rise is completely expected"), as an
equilibrium statement: if the date-`t + 1` news does not change expected future rates
(`ΔE_{t+1}i_{t+j} = 0`, `j ≥ 1`) and there is no surplus news, there is no inflation jump. -/
theorem expected_rise_equilibrium (hE : Equilibrium 𝔼 ρ ωh i sT v q rn infl) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hω : |ωh| < 1) (hsa : 𝔼.Adapted sT) (hsb : BoundedProc sT) (t : ℕ) (ω : Ω)
    (hs : ∀ j, innov 𝔼 t (sT (t + j + 1)) ω = 0)
    (hi : ∀ j, innov 𝔼 t (i (t + j + 1)) ω = 0) :
    innov 𝔼 t (infl (t + 1)) ω = 0 := by
  obtain ⟨hsum, h0⟩ := eqm_disinflation hE hρ0 hρ1 hω hsa hsb t ω hs
  have hx : ∀ j, (fun j => innov 𝔼 t (infl (t + j + 1)) ω) (j + 1) = 0 := fun j => by
    simp only [show t + (j + 1) + 1 = t + j + 2 by omega, innov_infl_eq_innov_i hE, hi]
  simpa using expected_rise_no_jump hx hsum h0

/-! ### A stochastic economy that delivers Figure 3.1 -/

namespace CoinEconomy

open TidyR6InnovGrowth.Boundary ExpectationsFiniteTree

/-- Cochrane (2023), §3.5.3 and Figure 3.1 (the hypotheses are met under genuine uncertainty): on
the coin-flip tree let the interest rate be `i_n = cs1` (the first flip `±1`) from date 1 on and
`0` at date 0, with zero surpluses. For `0 < ρ < 1` and `0 ≤ ω̂ < 1` the model has an equilibrium,
unique in the sense of `unique_eqm`, and in every state where the first flip is heads the date-1
response is exactly Figure 3.1: `ΔE_1π_1 = −ω̂/(1 − ω̂)` and `ΔE_1π_{2+j} = 1`. -/
theorem fig31_coin_economy {ρ ωh : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hω0 : 0 ≤ ωh) (hω1 : ωh < 1) :
    let iC : ℕ → Bool × Bool → ℝ := fun n => (if n = 0 then 0 else 1 : ℝ) • cs1
    let sC : ℕ → Bool × Bool → ℝ := fun _ _ => 0
    Equilibrium coinSystem ρ ωh iC sC (eqV coinSystem ρ sC) (eqQ coinSystem ωh iC)
      (eqRn coinSystem ωh iC) (eqInfl coinSystem ρ ωh iC sC) ∧
    ∀ b : Bool, innov coinSystem 0 (eqInfl coinSystem ρ ωh iC sC 1) (true, b) =
        -(ωh / (1 - ωh)) ∧
      ∀ j, innov coinSystem 0 (eqInfl coinSystem ρ ωh iC sC (j + 2)) (true, b) = 1 := by
  intro iC sC
  have hω : |ωh| < 1 := by rw [abs_of_nonneg hω0]; exact hω1
  have hia : coinSystem.Adapted iC := adapted_smul _ (by simp)
  have hib : BoundedProc iC := ⟨1, fun n ω => by
    simp only [iC, Pi.smul_apply, smul_eq_mul, abs_mul]
    have h1 := (cs1_ne_zero ω).2
    split_ifs <;> simp [h1]⟩
  have hsa : coinSystem.Adapted sC := fun t => coinSystem.const t 0
  have hsb : BoundedProc sC := ⟨0, fun _ _ => by simp [sC]⟩
  have hE := exists_eqm hρ0 hρ1 hω hia hib hsa hsb
  refine ⟨hE, fun b => ?_⟩
  have hs : ∀ j, innov coinSystem 0 (sC (0 + j + 1)) (true, b) = 0 := fun j => by
    rw [innov_apply]
    change coinSystem.E 1 (fun _ => (0 : ℝ)) (true, b) - coinSystem.E 0 (fun _ => (0 : ℝ))
      (true, b) = 0
    rw [coinSystem.const, coinSystem.const, sub_self]
  have hi : ∀ j, innov coinSystem 0 (iC (0 + j + 1)) (true, b) = 1 := fun j => by
    simp only [iC, innov_cs1, show 0 + j + 1 ≠ 0 by omega, ↓reduceIte, one_mul]
    simp [cs1, coinShock]
  have h := fig31_equilibrium hE hρ0 hρ1 hω0 hω1 hsa hsb 0 (true, b) hs hi
  exact ⟨by simpa using h.1, fun j => by simpa using h.2 j⟩

end CoinEconomy

end Cochrane.Generality.TidyR6Fig31Equilibrium
