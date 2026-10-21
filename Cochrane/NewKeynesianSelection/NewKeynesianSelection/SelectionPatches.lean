/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.LowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Equilibrium-selection patches

Cochrane (2023), Chapter 16, §16.10.1–16.10.6, pp. 383–394, with the Online Appendix A3,
§3.1.1–3.1.2, pp. 613–616. Perfect foresight throughout, except the minimum-state-variable
results, which hold for an arbitrary `ExpectationSystem`.

## Main results

* §16.10.1 (MSV), with (16.4) the canonical `SimplestModel.Eq164` and the MSV solution
  `SimplestModel.ar1Pi` (`SimplestModel.ar1Pi_eq164`): `msv_unique`, `msv_iff` (among
  `π_t = c u_t`, the unique
  solution of (16.4) is `−u_t/(φ − η)`, for every `φ ≠ η`, including passive `|φ| < 1`);
  `msv_none_of_eq`; `pf_explosive_not_msv`, `pf_passive_bounded_not_msv` (other solutions are not
  of MSV form, bounded ones included when `|φ| ≤ 1`); `msv_nonlinear_counterexample` (with a
  nonlinear `f`, `π_t = f(u_t)` admits explosive solutions under perfect foresight).
* §16.10.2 (stabilisations and ACK): `quantity_theory_growth`; the overlap regime `ACKEq`,
  `ack_inconsistent`, `ack_bounded`, `ack_iff`, `ack_prunes_inflation`, `ack_keeps_deflation`,
  `woodford_backstop_prunes`; the separated regime `StabEq`, `stabPath`, `stab_exists`,
  `stab_unique`, `stop_not_rule_out` ("stopping an inflation does not rule it out").
* §16.10.3 (fiscal trimming): BSGU `bsgu_real_debt`, `bsgu_tvc_violated`,
  `bsgu_no_equilibrium_to_lower`, `bsgu_target_survives`; Woodford's `μ̄` rule in Cochrane's
  notation `mubar_tvc_step`, `mubar_tvc_violated`, `mubar_deflation_violates`,
  `mubar_target_tvc_iff`; and the Woodford Chapter 2 versions restated in `WoodfordMuBar`.
* §16.10.4 (Bassetto): `bassetto_exit`, `bassetto_no_equilibrium`, `linear_rule_exit`.
* §16.10.5 (weird rules): `vertical_rule_exit`, `v_rule_unbounded`, `v_rule_unique_bounded`,
  `vRule`, `vRule_props`, `ahJump`, `ahJump_props`; tangency counterexample `tangentRule`,
  `tangent_rule_converges`.
* (16.31)–(16.32) (Schmitt-Grohé–Uribe): `eq1632_iff`, `eq1632_iff_path45`; the
  Schmitt-Grohé–Uribe example restated from Woodford Chapter 2 in `SGU`; and the correction
  `successor_exists_of_bounded_rule` (with a bounded continuous rule and `u_c ∘ L` continuous and
  positive on the range of rates, (16.32) always has a finite successor;
  `path_exists_of_bounded_rule`); and the converse example `bounded_rule_explosion` (bounded
  rule, `L(i) = 5 − i`, `u_c = 1/m`: no successor for `Π_t ∈ (1, 3/2)`).
* §16.10.6 (Sims 1994): `sims_tvc_violated`, `sims_tvc_violated_of_eventually_beta`,
  `sims_no_bite_above_beta`, `sims_slow_counterexample`.
* A3 §3.1.1–3.1.2: `a3_helicopter_pv`, `a3_helicopter_tvc_violated`, `a3_omo_real_const`,
  `a3_omo_nominal`, `a3_omo_debt_negative`, `a3_omo_tvc`.
-/

namespace Cochrane.NewKeynesianSelection.SelectionPatches

open Filter Topology
open Cochrane.NewKeynesianSelection.GlobalDynamics
open Cochrane.NewKeynesianSelection.LowerBound

/-! ## §16.10.1 Minimum state variables -/

/-- Cochrane (2023), §16.10.1, p. 385, "the only such solution is the 'locally bounded' choice
(16.6) `π_t = −u_t/(φ − η)`": if `u` is AR(1) and not identically zero, and `π_t = c u_t` solves
(16.4), then `φ ≠ η` and `c = −1/(φ − η)`. No restriction on `φ` is needed. -/
theorem msv_unique {Ω : Type*} (𝔼 : ExpectationSystem Ω) {φ η c : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hne : ∃ t ω, u t ω ≠ 0)
    (h : SimplestModel.Eq164 𝔼 φ u (fun t => c • u t)) : φ ≠ η ∧ c = -(φ - η)⁻¹ := by
  obtain ⟨t, ω, hω⟩ := hne
  have ht := congrFun (h t) ω
  rw [ExpectationSystem.E_smul, hu.2 t] at ht
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at ht
  have hkey : (c * (η - φ) - 1) * u t ω = 0 := by linarith
  have hc : c * (η - φ) = 1 := by
    have := (mul_eq_zero.mp hkey).resolve_right hω
    linarith
  have hφη : φ ≠ η := by
    intro he; rw [he, sub_self, mul_zero] at hc; exact zero_ne_one hc
  refine ⟨hφη, ?_⟩
  have : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  field_simp
  linarith

/-- Cochrane (2023), §16.10.1, p. 385: for AR(1) `u` not identically zero, `π_t = c u_t` solves
(16.4) if and only if `φ ≠ η` and `c = −1/(φ − η)`. The MSV criterion selects this solution for
every `φ ≠ η` — also in the passive case `|φ| < 1`, where it is not needed to rule out
explosions (so it is a selection device independent of the Taylor principle). -/
theorem msv_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) {φ η c : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hne : ∃ t ω, u t ω ≠ 0) :
    SimplestModel.Eq164 𝔼 φ u (fun t => c • u t) ↔ φ ≠ η ∧ c = -(φ - η)⁻¹ := by
  refine ⟨msv_unique 𝔼 hu hne, ?_⟩
  rintro ⟨hφη, rfl⟩
  exact SimplestModel.ar1Pi_eq164 𝔼 hφη hu

/-- Cochrane (2023), §16.10.1, p. 385: if `φ = η` (and `u` is not identically zero), (16.4) has
no MSV solution at all. -/
theorem msv_none_of_eq {Ω : Type*} (𝔼 : ExpectationSystem Ω) {η c : ℝ} {u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hne : ∃ t ω, u t ω ≠ 0) :
    ¬ SimplestModel.Eq164 𝔼 η u (fun t => c • u t) :=
  fun h => (msv_unique 𝔼 hu hne h).1 rfl

/-- Cochrane (2023), eq. (16.4), p. 364: under perfect foresight (16.4) is the deterministic
recursion `π_{t+1} = φπ_t + u_t`. -/
theorem simpleModel_pf_iff {φ : ℝ} {u infl : ℕ → Unit → ℝ} :
    SimplestModel.Eq164 perfectForesight φ u infl ↔
      ∀ t, infl (t + 1) () = φ * infl t () + u t () := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · simpa [perfectForesight] using congrFun h ()
  · funext ω
    simpa [perfectForesight] using h

/-- Cochrane (2023), §16.10.1, p. 385, "the minimum state variable criterion rules out the
explosive and sunspot solutions": under perfect foresight with `u_t = ηᵗu₀`, `φ ≠ η`, each
`π_t = −u_t/(φ − η) + φᵗδ₀` solves (16.4), and for `δ₀ ≠ 0` it is not of the form `c u_t`. -/
theorem pf_explosive_not_msv {φ η u0 δ0 : ℝ} (hφη : φ ≠ η) (hδ : δ0 ≠ 0) :
    (∀ t : ℕ, (-(φ - η)⁻¹ * (η ^ (t + 1) * u0) + φ ^ (t + 1) * δ0) =
      φ * (-(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0) + η ^ t * u0) ∧
      ¬ ∃ c : ℝ, ∀ t : ℕ, -(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0 = c * (η ^ t * u0) := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  refine ⟨fun t => ?_, ?_⟩
  · field_simp
    ring
  · rintro ⟨c, hc⟩
    have h0 := hc 0
    have h1 := hc 1
    simp only [pow_zero, one_mul, pow_one] at h0 h1
    have : (φ - η) * δ0 = 0 := by linear_combination h1 - η * h0
    rcases mul_eq_zero.mp this with h | h
    · exact hne h
    · exact hδ h

/-- Cochrane (2023), §16.10.1, p. 385, and §16.1, p. 364 ("if `‖φ‖ < 1`, this economy is stable
… but it remains indeterminate"): with `|φ| ≤ 1`, `|η| ≤ 1`, the non-MSV perfect-foresight
solutions `π_t = −u_t/(φ − η) + φᵗδ₀` are bounded, so the MSV criterion, not boundedness, is what
selects `−u_t/(φ − η)` in the passive case. -/
theorem pf_passive_bounded_not_msv {φ η u0 δ0 : ℝ} (hφ : |φ| ≤ 1) (hη : |η| ≤ 1) (t : ℕ) :
    |-(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0| ≤ |(φ - η)⁻¹| * |u0| + |δ0| := by
  have h1 : |η ^ t| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hη
  have h2 : |φ ^ t| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hφ
  calc |-(φ - η)⁻¹ * (η ^ t * u0) + φ ^ t * δ0|
      ≤ |-(φ - η)⁻¹ * (η ^ t * u0)| + |φ ^ t * δ0| := abs_add_le _ _
    _ = |(φ - η)⁻¹| * (|η ^ t| * |u0|) + |φ ^ t| * |δ0| := by
        rw [abs_mul, abs_neg, abs_mul, abs_mul]
    _ ≤ |(φ - η)⁻¹| * (1 * |u0|) + 1 * |δ0| := by
        gcongr
    _ = |(φ - η)⁻¹| * |u0| + |δ0| := by ring

/-- Cochrane (2023), §16.10.1, p. 385: the power identity behind the nonlinear MSV counterexample:
for `0 < η ≠ 1`, `φ > 0`, `u₀ > 0` and `κ = log φ/log η`, `(ηᵗu₀)^κ = φᵗ u₀^κ`. -/
theorem rpow_orbit {φ η u0 : ℝ} (hη0 : 0 < η) (hη1 : η ≠ 1) (hφ : 0 < φ) (hu0 : 0 < u0)
    (t : ℕ) :
    (η ^ t * u0) ^ (Real.log φ / Real.log η) = φ ^ t * u0 ^ (Real.log φ / Real.log η) := by
  have hlog : Real.log η ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h' | h' | h'
    · linarith
    · exact hη1 h'
    · linarith
  have hκ : η ^ (Real.log φ / Real.log η) = φ := by
    rw [Real.rpow_def_of_pos hη0, mul_div_cancel₀ _ hlog, Real.exp_log hφ]
  rw [Real.mul_rpow (pow_nonneg hη0.le t) hu0.le, ← Real.rpow_natCast η t, ← Real.rpow_mul hη0.le,
    mul_comm (t : ℝ), Real.rpow_mul hη0.le, hκ, Real.rpow_natCast]

/-- Cochrane (2023), §16.10.1, p. 385, imprecision: "the minimum state variable criterion says to
pick `π_t = f(u_t)`. The only such solution is … (16.6)" holds for linear `f` (`msv_iff`) but not
for arbitrary `f` under perfect foresight. With `u_t = ηᵗu₀`, `0 < η ≠ 1`, `u₀ > 0`, `φ > 0`,
`φ ≠ η`, the function `f(x) = −x/(φ − η) + x^κ`, `κ = log φ/log η`, gives a solution
`π_t = f(u_t)` of (16.4) that differs from (16.6) by `φᵗu₀^κ`, which explodes when `φ > 1`. -/
theorem msv_nonlinear_counterexample {φ η u0 : ℝ} (hη0 : 0 < η) (hη1 : η ≠ 1) (hφ : 0 < φ)
    (hφη : φ ≠ η) (hu0 : 0 < u0) :
    let f : ℝ → ℝ := fun x => -(φ - η)⁻¹ * x + x ^ (Real.log φ / Real.log η)
    (∀ t : ℕ, f (η ^ (t + 1) * u0) = φ * f (η ^ t * u0) + η ^ t * u0) ∧
      (∀ t : ℕ, f (η ^ t * u0) - (-(φ - η)⁻¹ * (η ^ t * u0)) =
        φ ^ t * u0 ^ (Real.log φ / Real.log η)) ∧
      (1 < φ → Tendsto (fun t : ℕ => f (η ^ t * u0) - (-(φ - η)⁻¹ * (η ^ t * u0))) atTop
        atTop) := by
  intro f
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  have hdev : ∀ t : ℕ, f (η ^ t * u0) - (-(φ - η)⁻¹ * (η ^ t * u0)) =
      φ ^ t * u0 ^ (Real.log φ / Real.log η) := fun t => by
    simp only [f, rpow_orbit hη0 hη1 hφ hu0 t]
    ring
  refine ⟨fun t => ?_, hdev, fun hφ1 => ?_⟩
  · simp only [f, rpow_orbit hη0 hη1 hφ hu0 t, rpow_orbit hη0 hη1 hφ hu0 (t + 1)]
    field_simp
    ring
  · simp only [hdev]
    exact (tendsto_pow_atTop_atTop_of_one_lt hφ1).atTop_mul_const
      (Real.rpow_pos_of_pos hu0 _)

/-! ## §16.10.2 Stabilisations and threats -/

/-- Cochrane (2023), §16.10.2, p. 389, "an economy with constant velocity and hence money demand
`M_t V = P_t y`": money growth equals inflation, `M_{t+1}/M_t = P_{t+1}/P_t`; so the money-growth
rule `M_{T+1}/M_T = μ` is the inflation target `Π_{T+1} = μ`. -/
theorem quantity_theory_growth {V y : ℝ} {M P : ℕ → ℝ} (hV : 0 < V) (hy : 0 < y)
    (hP : ∀ t, 0 < P t) (hqt : ∀ t, M t * V = P t * y) (t : ℕ) :
    M (t + 1) / M t = P (t + 1) / P t := by
  have hM : ∀ t, M t = P t * y / V := fun t => by rw [← hqt t]; field_simp
  rw [hM, hM]
  have := hP t
  field_simp

/-- Cochrane (2023), §16.10.2, p. 389 (Atkeson, Chari and Kehoe 2010; Christiano and Takahashi
2018): perfect-foresight equilibrium of the regime "Taylor rule `1 + i_t = (1 + r)Φ(Π_t)` until
and including the first period `T` with `Π_T > Π_U`; money-growth rule `Π_{t+1} = μ` from `T`
on": the two rules overlap at `T`. -/
def ACKEq (r : ℝ) (Φ : ℝ → ℝ) (PiU μ : ℝ) (infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < infl t) ∧ (∀ t, 0 ≤ i t) ∧ (∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ∧
    (∀ t, (∀ s < t, infl s ≤ PiU) → 1 + i t = (1 + r) * Φ (infl t)) ∧
    ∀ t, (∃ s ≤ t, PiU < infl s) → infl (t + 1) = μ

/-- Cochrane (2023), §16.10.2, p. 389, "an equilibrium cannot form at period `T`": at the first
period with `Π_T > Π_U`, an ACK equilibrium needs `Φ(Π_T) = μ` (a very high rate `i_T` and low
inflation `Π_{T+1} = μ` cannot both satisfy the Fisher equation). -/
theorem ack_inconsistent {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r)
    (h : ACKEq r Φ PiU μ infl i) {T : ℕ} (hT : PiU < infl T) (hbefore : ∀ s < T, infl s ≤ PiU) :
    Φ (infl T) = μ := by
  obtain ⟨-, -, hfis, htay, hmon⟩ := h
  have h1 := hmon T ⟨T, le_rfl, hT⟩
  rw [hfis, htay T hbefore, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul] at h1
  exact h1

/-- Cochrane (2023), §16.10.2, p. 389, "the inflationary path leading to `T` is not an
equilibrium": if `Φ(Π) ≠ μ` whenever `Π > Π_U`, no ACK equilibrium ever exceeds `Π_U`. -/
theorem ack_bounded {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r)
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) (h : ACKEq r Φ PiU μ infl i) : ∀ t, infl t ≤ PiU := by
  by_contra hcon
  push Not at hcon
  classical
  let T := Nat.find hcon
  have hT : PiU < infl T := Nat.find_spec hcon
  have hbefore : ∀ s < T, infl s ≤ PiU := fun s hs => not_lt.mp (Nat.find_min hcon hs)
  exact hΦμ _ hT (ack_inconsistent hr h hT hbefore)

/-- Cochrane (2023), §16.10.2, p. 389: when `Φ(Π) ≠ μ` above `Π_U`, the ACK equilibria are
exactly the Taylor-rule equilibria (16.29) that never exceed `Π_U`. -/
theorem ack_iff {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {infl i : ℕ → ℝ} (hr : 0 < 1 + r)
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) :
    ACKEq r Φ PiU μ infl i ↔
      (∀ t, 0 < infl t ∧ infl t ≤ PiU) ∧ (∀ t, infl (t + 1) = Φ (infl t)) ∧
        (∀ t, 1 + i t = (1 + r) * Φ (infl t)) ∧ ∀ t, (1 + r)⁻¹ ≤ Φ (infl t) := by
  constructor
  · intro h
    have hb := ack_bounded hr hΦμ h
    obtain ⟨hpos, hi, hfis, htay, -⟩ := h
    have htay' : ∀ t, 1 + i t = (1 + r) * Φ (infl t) := fun t => htay t fun s _ => hb s
    have hdyn : ∀ t, infl (t + 1) = Φ (infl t) := fun t => by
      rw [hfis, htay', ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    refine ⟨fun t => ⟨hpos t, hb t⟩, hdyn, htay', fun t => ?_⟩
    rw [← hdyn]
    exact (Hyperinflation.zero_bound_iff_scalar hr (hfis t)).mp (hi t)
  · rintro ⟨hb, hdyn, htay, hbd⟩
    refine ⟨fun t => (hb t).1, fun t => ?_, fun t => ?_, fun t _ => htay t, ?_⟩
    · have := (rule_respects_bound_iff (x := infl t) (Φ := Φ) hr).mpr (hbd t)
      rw [← htay] at this; linarith
    · rw [htay, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul, hdyn]
    · rintro t ⟨s, -, hs⟩
      exact absurd (hb s).2 (not_le.mpr hs)

/-- Cochrane (2023), §16.10.2, p. 389: the ACK regime prunes the inflationary equilibria of
Figure 16.2. If `Φ(Π) > Π` above `Π*` with `Φ` continuous there, `Π* ≤ Π_U`, and `Φ(Π) ≠ μ` above
`Π_U`, then no ACK equilibrium starts above `Π*`. -/
theorem ack_prunes_inflation {r : ℝ} {Φ : ℝ → ℝ} {Pis PiU μ : ℝ} {infl i : ℕ → ℝ}
    (hr : 0 < 1 + r) (habove : ∀ x, Pis < x → x < Φ x) (hcont : ContinuousOn Φ (Set.Ioi Pis))
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) (h : ACKEq r Φ PiU μ infl i) : infl 0 ≤ Pis := by
  by_contra h0
  push Not at h0
  have hdyn := ((ack_iff hr hΦμ).mp h).2.1
  have hbd := ((ack_iff hr hΦμ).mp h).1
  have hup : ∀ t, Pis < infl t ∧ infl t < infl (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hdyn]; exact habove _ h0⟩
    | succ n ih =>
      have h1 : Pis < infl (n + 1) := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hdyn (n + 1)]; exact habove _ h1⟩
  have hmono : Monotone infl := monotone_nat_of_le_succ fun t => (hup t).2.le
  rcases monotone_orbit_atTop_or_fixed hdyn hmono with htop | ⟨L, -, hLb, hfix⟩
  · obtain ⟨t, ht⟩ := (htop.eventually (eventually_gt_atTop PiU)).exists
    linarith [(hbd t).2]
  · have hL : Pis < L := lt_of_lt_of_le h0 (hLb 0)
    have := hfix (hcont.continuousAt (Ioi_mem_nhds hL))
    linarith [habove L hL]

/-- Cochrane (2023), §16.10.2, p. 389: the ACK regime does not prune the deflationary paths: if
`Φ` is monotone on `(0, Π*]`, `Φ(Π*) = Π*`, `Φ ≥ β` there and `Π* ≤ Π_U`, every `Π₀ ∈ (0, Π*]`
starts an ACK equilibrium (the plain Taylor-rule path). -/
theorem ack_keeps_deflation {r : ℝ} {Φ : ℝ → ℝ} {Pis PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hmono : MonotoneOn Φ (Set.Ioc 0 Pis)) (hfix : Φ Pis = Pis)
    (hbd : ∀ x ∈ Set.Ioc 0 Pis, (1 + r)⁻¹ ≤ Φ x) (hPiU : Pis ≤ PiU) (h0 : Pi0 ∈ Set.Ioc 0 Pis) :
    ACKEq r Φ PiU μ (fun t => Φ^[t] Pi0) (fun t => (1 + r) * Φ (Φ^[t] Pi0) - 1) := by
  have hmem : ∀ t, Φ^[t] Pi0 ∈ Set.Ioc 0 Pis := by
    intro t
    induction t with
    | zero => simpa using h0
    | succ n ih =>
      rw [orbit_succ]
      exact ⟨lt_of_lt_of_le (inv_pos.mpr hr) (hbd _ ih),
        hfix ▸ hmono ih ⟨by linarith [ih.2, ih.1], le_rfl⟩ ih.2⟩
  refine ⟨fun t => (hmem t).1, fun t => ?_, fun t => ?_, fun t _ => by ring, ?_⟩
  · have := (rule_respects_bound_iff (x := Φ^[t] Pi0) (Φ := Φ) hr).mpr (hbd _ (hmem t))
    exact this
  · dsimp only
    rw [orbit_succ]; field_simp; ring
  · rintro t ⟨s, -, hs⟩
    exact absurd ((hmem s).2.trans hPiU) (not_le.mpr hs)

/-- Cochrane (2023), §16.10.2, pp. 388–389, Woodford's commodity backstop under a Taylor rule:
"if a government continues to follow the Taylor rule … even after it has switched to a commodity
standard that requires low nominal interest rates, then, yes, no equilibrium can form". A
commodity peg fixes the price level, `Π_{T+1} = 1`: the ACK structure with `μ = 1`; with
`1 ≤ Π* ≤ Π_U` and `Φ(Π) > Π` above `Π*` (continuous), no equilibrium starts above `Π*`. -/
theorem woodford_backstop_prunes {r : ℝ} {Φ : ℝ → ℝ} {Pis PiU : ℝ} {infl i : ℕ → ℝ}
    (hr : 0 < 1 + r) (hPis1 : 1 ≤ Pis) (hPiU : Pis ≤ PiU) (habove : ∀ x, Pis < x → x < Φ x)
    (hcont : ContinuousOn Φ (Set.Ioi Pis)) (h : ACKEq r Φ PiU 1 infl i) : infl 0 ≤ Pis :=
  ack_prunes_inflation hr habove hcont
    (fun x hx => ne_of_gt (lt_trans (by linarith) (habove x (by linarith)))) h

/-- Cochrane (2023), §16.10.2, p. 387, "if the government separates by one period the inflation
and its stabilization": the Taylor rule applies at `t` while `Π_s ≤ Π_U` for all `s ≤ t`; from
the first period `T` with `Π_T > Π_U` on, only the money-growth rule `Π_{t+1} = μ` applies. -/
def StabEq (r : ℝ) (Φ : ℝ → ℝ) (PiU μ : ℝ) (infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < infl t) ∧ (∀ t, 0 ≤ i t) ∧ (∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ∧
    (∀ t, (∀ s ≤ t, infl s ≤ PiU) → 1 + i t = (1 + r) * Φ (infl t)) ∧
    ∀ t, (∃ s ≤ t, PiU < infl s) → infl (t + 1) = μ

/-- Cochrane (2023), §16.10.2, p. 387: the stabilised path — the Taylor orbit `Φ^[t](Π₀)` until
it first exceeds `Π_U`, and `μ` from the next period on. -/
noncomputable def stabPath (Φ : ℝ → ℝ) (PiU μ Pi0 : ℝ) (t : ℕ) : ℝ :=
  if ∃ s < t, PiU < Φ^[s] Pi0 then μ else Φ^[t] Pi0

/-- Cochrane (2023), §16.10.2, p. 387: while the stabilised path has stayed at or below `Π_U`, it
coincides with the Taylor orbit, and so has the orbit. -/
theorem stabPath_taylor {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} {t : ℕ}
    (h : ∀ s ≤ t, stabPath Φ PiU μ Pi0 s ≤ PiU) :
    (∀ s ≤ t, Φ^[s] Pi0 ≤ PiU) ∧ ∀ s ≤ t, stabPath Φ PiU μ Pi0 s = Φ^[s] Pi0 := by
  have hno : ∀ s ≤ t, Φ^[s] Pi0 ≤ PiU := by
    by_contra hcon
    push Not at hcon
    classical
    have hex : ∃ s, s ≤ t ∧ PiU < Φ^[s] Pi0 := hcon
    let s0 := Nat.find hex
    have hs0 := Nat.find_spec hex
    have hmin : ∀ s < s0, Φ^[s] Pi0 ≤ PiU := fun s hs => by
      by_contra hc
      exact Nat.find_min hex hs ⟨by have := hs0.1; omega, not_le.mp hc⟩
    have heq : stabPath Φ PiU μ Pi0 s0 = Φ^[s0] Pi0 := by
      unfold stabPath
      rw [ite_eq_right_iff]
      rintro ⟨s, hs, hlt⟩
      exact absurd (hmin s hs) (not_le.mpr hlt)
    have := h s0 hs0.1
    rw [heq] at this
    exact absurd this (not_le.mpr hs0.2)
  refine ⟨hno, fun s hs => ?_⟩
  unfold stabPath
  rw [ite_eq_right_iff]
  rintro ⟨s', hs', hlt⟩
  exact absurd (hno s' (by omega)) (not_le.mpr hlt)

/-- Cochrane (2023), §16.10.2, p. 387: once the stabilised path has exceeded `Π_U`, it equals
`μ` from the next period on. -/
theorem stabPath_money {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} {t : ℕ}
    (h : ∃ s ≤ t, PiU < stabPath Φ PiU μ Pi0 s) : stabPath Φ PiU μ Pi0 (t + 1) = μ := by
  obtain ⟨s, hs, hlt⟩ := h
  unfold stabPath
  rw [ite_eq_left_iff]
  intro hc
  exfalso
  apply hc
  by_cases hex : ∃ s' < s, PiU < Φ^[s'] Pi0
  · obtain ⟨s', hs', h'⟩ := hex
    exact ⟨s', by omega, h'⟩
  · unfold stabPath at hlt
    simp only [hex, ↓reduceIte] at hlt
    exact ⟨s, by omega, hlt⟩

/-- Cochrane (2023), §16.10.2, p. 387: the stabilised path is an equilibrium of the separated
regime for every `Π₀ > 0`, provided the Taylor rule respects the zero bound (`Φ ≥ β` on `(0, ∞)`)
and the money-growth target does (`μ ≥ β`). -/
theorem stab_exists {r : ℝ} {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hΦ : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (hμ : (1 + r)⁻¹ ≤ μ) (hPi0 : 0 < Pi0) :
    StabEq r Φ PiU μ (stabPath Φ PiU μ Pi0)
      (fun t => (1 + r) * stabPath Φ PiU μ Pi0 (t + 1) - 1) ∧
      stabPath Φ PiU μ Pi0 0 = Pi0 := by
  have hβ : 0 < (1 + r)⁻¹ := inv_pos.mpr hr
  have horb : ∀ t, 0 < Φ^[t] Pi0 := by
    intro t
    induction t with
    | zero => simpa using hPi0
    | succ n ih => rw [orbit_succ]; exact lt_of_lt_of_le hβ (hΦ _ ih)
  have hge : ∀ t, (1 + r)⁻¹ ≤ stabPath Φ PiU μ Pi0 (t + 1) := by
    intro t
    unfold stabPath
    split_ifs
    · exact hμ
    · rw [orbit_succ]; exact hΦ _ (horb t)
  have hpos : ∀ t, 0 < stabPath Φ PiU μ Pi0 t := by
    intro t
    cases t with
    | zero => simp [stabPath, hPi0]
    | succ n => exact lt_of_lt_of_le hβ (hge n)
  refine ⟨⟨hpos, fun t => ?_, fun t => ?_, fun t ht => ?_, fun t ht => stabPath_money ht⟩,
    by simp [stabPath]⟩
  · have := (rule_respects_bound_iff (x := 0) (Φ := fun _ => stabPath Φ PiU μ Pi0 (t + 1))
      hr).mpr (hge t)
    exact this
  · field_simp; ring
  · obtain ⟨hno, heq⟩ := stabPath_taylor ht
    have h1 : stabPath Φ PiU μ Pi0 (t + 1) = Φ^[t + 1] Pi0 := by
      unfold stabPath
      rw [ite_eq_right_iff]
      rintro ⟨s, hs, hlt⟩
      exact absurd (hno s (by omega)) (not_le.mpr hlt)
    dsimp only
    rw [h1, heq t le_rfl, orbit_succ]
    ring

/-- Cochrane (2023), §16.10.2, p. 387: the separated regime determines the path given `Π₀`: two
equilibria with the same initial inflation coincide. -/
theorem stab_unique {r : ℝ} {Φ : ℝ → ℝ} {PiU μ : ℝ} {a b ia ib : ℕ → ℝ} (hr : 0 < 1 + r)
    (ha : StabEq r Φ PiU μ a ia) (hb : StabEq r Φ PiU μ b ib) (h0 : a 0 = b 0) :
    a = b ∧ ia = ib := by
  obtain ⟨-, -, hfa, hta, hma⟩ := ha
  obtain ⟨-, -, hfb, htb, hmb⟩ := hb
  have hdyn_a : ∀ t, (∀ s ≤ t, a s ≤ PiU) → a (t + 1) = Φ (a t) := fun t h => by
    rw [hfa, hta t h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hdyn_b : ∀ t, (∀ s ≤ t, b s ≤ PiU) → b (t + 1) = Φ (b t) := fun t h => by
    rw [hfb, htb t h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hall : ∀ t, ∀ s ≤ t, a s = b s := by
    intro t
    induction t with
    | zero => intro s hs; rw [Nat.le_zero.mp hs]; exact h0
    | succ n ih =>
      intro s hs
      rcases Nat.lt_or_ge s (n + 1) with hlt | hge
      · exact ih s (by omega)
      · have hs' : s = n + 1 := by omega
        subst hs'
        by_cases hc : ∀ s ≤ n, a s ≤ PiU
        · have hc' : ∀ s ≤ n, b s ≤ PiU := fun s hs => (ih s hs) ▸ hc s hs
          rw [hdyn_a n hc, hdyn_b n hc', ih n le_rfl]
        · push Not at hc
          obtain ⟨s, hs, hlt⟩ := hc
          rw [hma n ⟨s, hs, hlt⟩, hmb n ⟨s, hs, (ih s hs) ▸ hlt⟩]
  have hab : a = b := funext fun t => hall t t le_rfl
  refine ⟨hab, funext fun t => ?_⟩
  have h1 := hfa t
  have h2 := hfb t
  rw [hab] at h1
  rw [h1] at h2
  have := mul_left_cancel₀ (inv_ne_zero hr.ne') h2
  linarith

/-- Cochrane (2023), §16.10.2, p. 386, "if a multiple-equilibrium inflation or deflation breaks
out, and if the government successfully stops the inflation … then the inflation and its end
remain an equilibrium path": in the separated regime every `Π₀ > 0` starts exactly one
equilibrium; it follows the Taylor orbit up to the first period `T` at which the orbit exceeds
`Π_U`, and is stabilised at `μ` afterwards. Stopping an inflation does not rule it out. -/
theorem stop_not_rule_out {r : ℝ} {Φ : ℝ → ℝ} {PiU μ Pi0 : ℝ} (hr : 0 < 1 + r)
    (hΦ : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (hμ : (1 + r)⁻¹ ≤ μ) (hPi0 : 0 < Pi0) :
    (∃ infl i : ℕ → ℝ, StabEq r Φ PiU μ infl i ∧ infl 0 = Pi0) ∧
      (∀ infl i infl' i' : ℕ → ℝ, StabEq r Φ PiU μ infl i → StabEq r Φ PiU μ infl' i' →
        infl 0 = Pi0 → infl' 0 = Pi0 → infl = infl') ∧
      ∀ T, PiU < Φ^[T] Pi0 → (∀ s < T, Φ^[s] Pi0 ≤ PiU) →
        (∀ t ≤ T, stabPath Φ PiU μ Pi0 t = Φ^[t] Pi0) ∧
          ∀ t, T < t → stabPath Φ PiU μ Pi0 t = μ := by
  refine ⟨⟨_, _, stab_exists hr hΦ hμ hPi0⟩, fun a ia b ib ha hb h0 h0' =>
    (stab_unique hr ha hb (h0.trans h0'.symm)).1, fun T hT hbefore => ⟨fun t ht => ?_,
      fun t ht => ?_⟩⟩
  · unfold stabPath
    rw [ite_eq_right_iff]
    rintro ⟨s, hs, hlt⟩
    exact absurd (hbefore s (by omega)) (not_le.mpr hlt)
  · unfold stabPath
    rw [ite_eq_left_iff]
    intro hc
    exact absurd ⟨T, ht, hT⟩ hc

/-! ## §16.10.3 Fiscal equilibrium trimming -/

/-- Cochrane (2023), §16.10.3, p. 390, Benhabib, Schmitt-Grohé and Uribe (2002): with surpluses
`s_t = θ(Π_t) B_{t−1}/P_t`, (16.30) becomes `b_{t+1} = (1 + r)(1 − θ(Π_t)) b_t` for real debt
`b_t = B_{t−1}/P_t`. -/
theorem bsgu_real_debt {r θ bt st bt1 : ℝ} (hflow : bt1 = (1 + r) * (bt - st))
    (hs : st = θ * bt) : bt1 = (1 + r) * (1 - θ) * bt := by
  rw [hflow, hs]; ring

/-- Cochrane (2023), §16.10.3, p. 390, "the government lowers taxes, real debt grows explosively,
the consumer's transversality condition is violated": if `b₀ > 0`,
`b_{t+1} = (1 + r)(1 − θ_t)b_t` with `θ_t < 1`, and eventually `θ_t ≤ θ̄ < 0`, then the discounted
real debt `βᵗb_t` diverges to `+∞`. -/
theorem bsgu_tvc_violated {r : ℝ} {b θ : ℕ → ℝ} (hr : 0 < 1 + r) (hb0 : 0 < b 0)
    (hflow : ∀ t, b (t + 1) = (1 + r) * (1 - θ t) * b t) (hθ1 : ∀ t, θ t < 1) {T0 : ℕ}
    {θbar : ℝ} (hθbar : θbar < 0) (hev : ∀ t, T0 ≤ t → θ t ≤ θbar) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * b T) atTop atTop := by
  set x : ℕ → ℝ := fun T => (1 + r)⁻¹ ^ T * b T with hx
  have hstep : ∀ T, x (T + 1) = (1 - θ T) * x T := fun T => by
    simp only [hx, hflow, pow_succ]
    field_simp
  have hpos : ∀ T, 0 < x T := by
    intro T
    induction T with
    | zero => simpa [hx] using hb0
    | succ n ih => rw [hstep]; exact mul_pos (by linarith [hθ1 n]) ih
  have hgrow : ∀ n, (1 - θbar) ^ n * x T0 ≤ x (T0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, hstep, pow_succ]
      have h1 : 1 - θbar ≤ 1 - θ (T0 + n) := by linarith [hev (T0 + n) (by omega)]
      calc (1 - θbar) ^ n * (1 - θbar) * x T0 = (1 - θbar) * ((1 - θbar) ^ n * x T0) := by ring
        _ ≤ (1 - θ (T0 + n)) * x (T0 + n) := by
          have := pow_pos (by linarith : (0 : ℝ) < 1 - θbar) n
          have := hpos T0
          exact mul_le_mul h1 ih (by positivity) (by linarith)
  have hlim : Tendsto (fun T => (1 - θbar) ^ (T - T0) * x T0) atTop atTop :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp
      (tendsto_sub_atTop_nat T0)).atTop_mul_const (hpos T0)
  refine tendsto_atTop_mono' atTop ?_ hlim
  filter_upwards [eventually_ge_atTop T0] with T hT
  have := hgrow (T - T0)
  rwa [Nat.add_sub_cancel' hT] at this

/-- Cochrane (2023), §16.10.3, pp. 390–391, "a deflationary trap is not a possible rational
expectations equilibrium": with the BSGU surplus rule `s_t = θ(Π_t)B_{t−1}/P_t`, `θ < 1`,
`θ` continuous at `Π_L` with `θ(Π_L) < 0`, and positive initial debt, no equilibrium (in the sense
of `LowerBound.IsEquilibrium`) has inflation converging to `Π_L`. -/
theorem bsgu_no_equilibrium_to_lower {r : ℝ} {Φ θ : ℝ → ℝ} {Pm1 PL : ℝ} {P i s D : ℕ → ℝ}
    (hr : 0 < 1 + r) (h : IsEquilibrium r Φ Pm1 P i s D)
    (hrule : ∀ t, s t = θ (infl Pm1 P t) * (D t / P t)) (hD0 : 0 < D 0)
    (hθ1 : ∀ x, θ x < 1) (hθc : ContinuousAt θ PL) (hθL : θ PL < 0) :
    ¬ Tendsto (infl Pm1 P) atTop (𝓝 PL) := by
  intro hlim
  obtain ⟨-, -, hreal, htvc⟩ := equilibrium_dynamics hr h
  have hP := h.2.1
  have hflow : ∀ t, D (t + 1) / P (t + 1) = (1 + r) * (1 - θ (infl Pm1 P t)) * (D t / P t) :=
    fun t => bsgu_real_debt (hreal t) (hrule t)
  have hev : ∀ᶠ t in atTop, θ (infl Pm1 P t) < θ PL / 2 :=
    (hθc.tendsto.comp hlim).eventually (gt_mem_nhds (by linarith))
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hev
  have hdiv := bsgu_tvc_violated (b := fun t => D t / P t) hr (div_pos hD0 (hP 0)) hflow
    (fun t => hθ1 _) (θbar := θ PL / 2) (by linarith) (fun t ht => (hT0 t ht).le)
  have h0 := htvc 0
  simp only [zero_add] at h0
  exact not_tendsto_nhds_of_tendsto_atTop hdiv 0 h0

/-- Cochrane (2023), §16.10.3, p. 390: with `θ(Π*) = r/(1+r)` (passive at the target) the target
`Π_t ≡ Π*` remains an equilibrium under the BSGU surplus rule. -/
theorem bsgu_target_survives {r : ℝ} {Φ θ : ℝ → ℝ} {Pm1 Pis : ℝ} (D0 : ℝ) (hr : 0 < r)
    (hPm1 : 0 < Pm1) (hfix : Φ Pis = Pis) (hβ : (1 + r)⁻¹ ≤ Pis) (hθ : θ Pis = r / (1 + r)) :
    ∃ P i s D : ℕ → ℝ, IsEquilibrium r Φ Pm1 P i s D ∧ (∀ t, infl Pm1 P t = Pis) ∧
      ∀ t, s t = θ (infl Pm1 P t) * (D t / P t) := by
  have hc : ∀ t, Φ^[t] Pis = Pis := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [orbit_succ, ih, hfix]
  have hPis : 0 < Pis := lt_of_lt_of_le (inv_pos.mpr (by linarith)) hβ
  obtain ⟨P, i, s, D, h, -, hinfl, hs, -⟩ := equilibrium_exists (Φ := Φ) (Pi0 := Pis) D0 hr
    hPm1 hPis fun t => by rw [hc, hfix]; exact hβ
  refine ⟨P, i, s, D, h, fun t => by rw [hinfl, hc], fun t => ?_⟩
  rw [hs, hinfl, hc, hθ]

/-- Cochrane (2023), §16.10.3, p. 390, Woodford's rule "let total nominal government liabilities
`D_t` … grow at a constant rate `μ̄`", in Cochrane's notation: with `P_{T+1} = Π_{T+1}P_T` and
`D_{T+1} = μ̄D_T`, the transversality term `βᵀD_T/P_T` is multiplied each period by
`βμ̄/Π_{T+1}`. -/
theorem mubar_tvc_step {r μ : ℝ} {infl P D : ℕ → ℝ} (hP : ∀ t, 0 < P t)
    (hinfl : ∀ t, 0 < infl t) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (T : ℕ) :
    (1 + r)⁻¹ ^ (T + 1) * (D (T + 1) / P (T + 1)) =
      (1 + r)⁻¹ ^ T * (D T / P T) * ((1 + r)⁻¹ * μ / infl (T + 1)) := by
  rw [hD, hPrec, pow_succ]
  have := hP T
  have := hinfl (T + 1)
  field_simp

/-- Cochrane (2023), §16.10.3, p. 390, Woodford's `μ̄` rule: if eventually `Π_{T+1} ≤ βμ̄` and
nominal liabilities are positive, the transversality term is eventually nondecreasing and
positive, so the transversality condition fails. -/
theorem mubar_tvc_violated {r μ : ℝ} {infl P D : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ t, 0 < P t)
    (hinfl : ∀ t, 0 < infl t) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t) {T0 : ℕ}
    (hev : ∀ T, T0 ≤ T → infl (T + 1) ≤ (1 + r)⁻¹ * μ) :
    ¬ Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0) := by
  set v : ℕ → ℝ := fun T => (1 + r)⁻¹ ^ T * (D T / P T) with hv
  have hpos : ∀ T, 0 < v T := fun T => by
    have := hDpos T; have := hP T; have := inv_pos.mpr hr; positivity
  have hmono : ∀ n, v T0 ≤ v (T0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc]
      simp only [hv] at ih ⊢
      rw [mubar_tvc_step hP hinfl hPrec hD]
      have h1 : 1 ≤ (1 + r)⁻¹ * μ / infl (T0 + n + 1) :=
        (one_le_div (hinfl _)).mpr (hev _ (by omega))
      have := hpos (T0 + n)
      simp only [hv] at this
      nlinarith
  intro h
  have hev' : ∀ᶠ T in atTop, v T0 ≤ v T := by
    filter_upwards [eventually_ge_atTop T0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hmono n
  have := ge_of_tendsto h hev'
  linarith [hpos T0]

/-- Cochrane (2023), §16.10.3, p. 390, "thus, in the case of an appropriate fiscal policy rule, a
deflationary trap is not a possible rational expectations equilibrium": with liabilities growing
at `μ̄`, every path converging to a point `Π_L < βμ̄` violates the transversality condition (for
`Π_L = β`, at the zero bound, this needs only `μ̄ > 1`). -/
theorem mubar_deflation_violates {r μ PL : ℝ} {infl P D : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ t, 0 < P t) (hinfl : ∀ t, 0 < infl t) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t) (hlim : Tendsto infl atTop (𝓝 PL))
    (hPL : PL < (1 + r)⁻¹ * μ) :
    ¬ Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0) := by
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hPL))
  exact mubar_tvc_violated hr hP hinfl hPrec hD hDpos (T0 := T0) fun T hT =>
    (hT0 (T + 1) (by omega)).le

/-- Cochrane (2023), §16.10.3, p. 390: along the target path `Π_t ≡ Π*` the transversality term
is `(βμ̄/Π*)ᵀ` times its initial value, so the target satisfies the transversality condition iff
`βμ̄ < Π*`. With `Π_L < βμ̄ < Π*` the `μ̄` rule removes the deflations and keeps the target. -/
theorem mubar_target_tvc_iff {r μ Pis : ℝ} {P D : ℕ → ℝ} (hr : 0 < 1 + r) (hμ : 0 < μ)
    (hPis : 0 < Pis) (hP : ∀ t, 0 < P t) (hPrec : ∀ t, P (t + 1) = Pis * P t)
    (hD : ∀ t, D (t + 1) = μ * D t) (hDpos : ∀ t, 0 < D t) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * (D T / P T)) atTop (𝓝 0) ↔ (1 + r)⁻¹ * μ < Pis := by
  have hval : ∀ T, (1 + r)⁻¹ ^ T * (D T / P T) = D 0 / P 0 * ((1 + r)⁻¹ * μ / Pis) ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [mubar_tvc_step (infl := fun _ => Pis) hP (fun _ => hPis) hPrec hD, ih, pow_succ]
      ring
  have h0 : 0 < D 0 / P 0 := div_pos (hDpos 0) (hP 0)
  have hr0 : 0 ≤ (1 + r)⁻¹ * μ / Pis := by have := inv_pos.mpr hr; positivity
  simp only [hval]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hr1 : 1 ≤ (1 + r)⁻¹ * μ / Pis := (one_le_div hPis).mpr hcon
    have hev : ∀ᶠ T in atTop, D 0 / P 0 ≤ D 0 / P 0 * ((1 + r)⁻¹ * μ / Pis) ^ T :=
      Eventually.of_forall fun T => le_mul_of_one_le_right h0.le (one_le_pow₀ hr1)
    have := ge_of_tendsto h hev
    linarith
  · intro h
    have hr1 : (1 + r)⁻¹ * μ / Pis < 1 := (div_lt_one hPis).mpr h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (D 0 / P 0)

/-! ## Woodford's `μ̄` rule, restated from the Woodford Chapter 2 project -/

namespace WoodfordMuBar

/-! ## The Taylor-rule version: nominal liabilities growing at `μ̄` (pp. 132–133) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), (1.24), p. 72, along a perfect-foresight path: the transversality term
`β^T λ(i_T) D_T/P_T` with `i_T = φ(Π_T)`. -/
noncomputable def tvcValue (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ P D : ℕ → ℝ) (T : ℕ) : ℝ :=
  β ^ T * lam (φ (Pi_ T)) * D T / P T

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, displayed identity: when `P_{t+1} = Π_{t+1}P_t`,
`D_{t+1} = μ̄D_t` and (4.5) holds,
`β^{T+1}λ_{T+1}D_{T+1}/P_{T+1} = β^Tλ_TD_T/P_T · μ̄/(1 + i_T)`. -/
theorem tvcValue_succ {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t) (T : ℕ) :
    tvcValue β lam φ Pi_ P D (T + 1) = tvcValue β lam φ Pi_ P D T * (μ / (1 + φ (Pi_ T))) := by
  have h45 := hpath.2 T
  have hl1 := hlam (T + 1)
  have hl := hlam T
  have hPi := hpath.1 (T + 1)
  have hφT := hφ T
  have hPT := hP T
  have hlam1 : lam (φ (Pi_ (T + 1))) = Pi_ (T + 1) * lam (φ (Pi_ T)) / (β * (1 + φ (Pi_ T))) := by
    rw [div_eq_div_iff hl1.ne' hl.ne'] at h45
    rw [eq_div_iff (by positivity)]
    linarith
  unfold tvcValue
  rw [hlam1, hPrec, hD, pow_succ]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), pp. 132–133 (error E4 corrected): if from some date on `1 + i_T ≤ μ̄`, the
transversality term is nondecreasing and positive from that date, so the transversality
condition (1.24) is violated. -/
theorem taylor_tvc_violated_of_eventually_le {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hev : ∃ t0, ∀ T, t0 ≤ T → 1 + φ (Pi_ T) ≤ μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t0, ht0⟩ := hev
  have hpos : ∀ T, 0 < tvcValue β lam φ Pi_ P D T := fun T => by
    unfold tvcValue; have := hlam T; have := hDpos T; have := hP T; positivity
  have hmono : ∀ n, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D (t0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, tvcValue_succ hβ hpath hlam hφ hP hPrec hD]
      have h1 : 1 ≤ μ / (1 + φ (Pi_ (t0 + n))) :=
        (one_le_div (hφ _)).mpr (ht0 _ (Nat.le_add_right _ _))
      nlinarith [hpos (t0 + n)]
  intro h
  have hev : ∀ᶠ T in atTop, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D T := by
    filter_upwards [eventually_ge_atTop t0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hmono n
  have := ge_of_tendsto h hev
  linarith [hpos t0]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, error E4: the printed claim "there must exist a date `t` such that
`1 + φ(Π_T) ≥ μ̄` for all `T ≥ t`" is false along any deflationary path converging to a point
`Π**` where `φ` is continuous with `1 + φ(Π**) < μ̄` (in Figure 2.4, `Π** = β`, `φ(β) = 0`,
`μ̄ > 1`). -/
theorem e4_printed_inequality_false {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ¬ ∃ t, ∀ T, t ≤ T → μ ≤ 1 + φ (Pi_ T) := by
  rintro ⟨t, ht⟩
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  have h2 : ∀ᶠ T in atTop, μ ≤ 1 + φ (Pi_ T) := by
    filter_upwards [eventually_ge_atTop t] with T hT using ht T hT
  have := ge_of_tendsto h1 h2
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, error E4 corrected: under the same hypotheses there is a date after
which `1 + φ(Π_T) ≤ μ̄` (indeed `<`). -/
theorem e4_corrected_inequality {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ∃ t, ∀ T, t ≤ T → 1 + φ (Pi_ T) ≤ μ := by
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  obtain ⟨t, ht⟩ := eventually_atTop.mp (h1.eventually (gt_mem_nhds hμ))
  exact ⟨t, fun T hT => (ht T hT).le⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, "even if interest rates level off sooner, so that there exists a
lower steady-state inflation rate `Π** > β`, the same argument works as long as `μ̄ > β⁻¹Π**`":
a path of (4.5) converging to a steady state `Π**` (so `1 + φ(Π**) = β⁻¹Π**`) with `φ` continuous
there and `μ̄ > β⁻¹Π**` violates the transversality condition. -/
theorem deflation_tvc_violated {β μ Pss : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ0 : ∀ t, 0 ≤ φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss)
    (hss : 1 + φ Pss = Pss / β) (hμ : Pss / β < μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) :=
  taylor_tvc_violated_of_eventually_le hβ hpath hlam (fun t => by linarith [hφ0 t]) hP hPrec hD
    hDpos (e4_corrected_inequality hlim hcont (by rw [hss]; exact hμ))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 132: if `φ(Π) = 0` for all `Π ≤ Π̲` with `Π̲ > β`, a path of (4.5) that is
eventually below `Π̲` has `i_T = 0` and then `Π_{T+1} = β` from that date on. -/
theorem zero_bound_inflation_eq_beta {β Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hpath : IsPath45 β lam φ Pi_) (hlam0 : 0 < lam 0) (hzero : ∀ x, x ≤ Plow → φ x = 0)
    {t : ℕ} (ht : ∀ T, t ≤ T → Pi_ T ≤ Plow) : ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β := by
  intro T hT
  have h1 := hzero _ (ht T hT)
  have h2 := hzero _ (ht (T + 1) (by omega))
  have h45 := hpath.2 T
  rw [h1, h2, add_zero, mul_one] at h45
  exact ⟨h1, by rwa [div_left_inj' hlam0.ne'] at h45⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 132, "then any deflationary solution to (4.5) involves a zero nominal
interest rate in each period after some finite date `t`, which in turn implies that `Π_T = β`
for all `T ≥ t + 1`. It follows that … the transversality condition (1.24) is violated": with
`φ = 0` on `(−∞, Π̲]`, `Π̲ > β`, `D` growing at `μ̄ ≥ 1`, a path of (4.5) converging to `β`
eventually has `i = 0` and `Π = β`, and violates (1.24). -/
theorem zero_bound_tvc_violated {β μ Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hPlow : β < Plow) (hμ : 1 ≤ μ) (hpath : IsPath45 β lam φ Pi_)
    (hlam : ∀ t, 0 < lam (φ (Pi_ t))) (hlam0 : 0 < lam 0) (hφ0 : ∀ t, 0 ≤ φ (Pi_ t))
    (hzero : ∀ x, x ≤ Plow → φ x = 0) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 β)) :
    (∃ t, ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β) ∧
      ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t, ht⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hPlow))
  have hz := zero_bound_inflation_eq_beta hpath hlam0 hzero (fun T hT => (ht T hT).le)
  refine ⟨⟨t, hz⟩, taylor_tvc_violated_of_eventually_le hβ hpath hlam
    (fun s => by linarith [hφ0 s]) hP hPrec hD hDpos ⟨t, fun T hT => ?_⟩⟩
  rw [(hz T hT).1]; linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), p. 133, "even if `φ(Π) > 0` for all `Π > β`, as long as
`φ(Π) < (Π − β)/β` for all `β < Π < Π*`, one can still exclude self-fulfilling deflations in the
case of any fiscal policy that ensures a growth rate `μ̄ > 1` for government liabilities": under
the hypotheses of Figure 2.4 (`GlobalDynamics.self_fulfilling_deflation45`), every solution of
(4.5) starting in `(β, Π*)` violates the transversality condition (1.24). -/
theorem fig24_deflations_violate_tvc {β Pis μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hμ : 1 < μ) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) : ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  have hlim := (self_fulfilling_deflation45 hβ hlam hanti hlamc hmono hφ0 hcont hφβ hbelow
    hpath h0).2.2
  exact deflation_tvc_violated hβ hpath (fun t => hlam _ (hφ0 _ (hpath.1 t)))
    (fun t => hφ0 _ (hpath.1 t)) hP hPrec hD hDpos hlim
    (hcont.continuousAt (Ioi_mem_nhds hβ)) (by rw [hφβ, div_self hβ.ne']; ring)
    (by rw [div_self hβ.ne']; exact hμ)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.3).
Woodford (2003), pp. 132–133 (implicit): along the target path `Π_t ≡ Π*` (with
`1 + φ(Π*) = Π*/β`) the transversality term is `(βμ̄/Π*)^T` times its initial value, so the target
equilibrium satisfies (1.24) iff `βμ̄ < Π*` (given `μ̄ > 0`). -/
theorem target_tvc_iff {β μ Pis : ℝ} {lam φ : ℝ → ℝ} {P D : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hPis : 0 < Pis) (htarget : 1 + φ Pis = Pis / β) (hlam : 0 < lam (φ Pis))
    (hP : ∀ t, 0 < P t) (hPrec : ∀ t, P (t + 1) = Pis * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    Tendsto (tvcValue β lam φ (fun _ => Pis) P D) atTop (𝓝 0) ↔ β * μ < Pis := by
  have hpath : IsPath45 β lam φ (fun _ => Pis) := ⟨fun _ => hPis, fun _ => by
    simp only [htarget]; field_simp⟩
  have hval : ∀ T, tvcValue β lam φ (fun _ => Pis) P D T =
      tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [tvcValue_succ hβ hpath (fun _ => hlam) (fun _ => by rw [htarget]; positivity) hP hPrec
        hD, ih, htarget, pow_succ]
      field_simp
  have h0 : 0 < tvcValue β lam φ (fun _ => Pis) P D 0 := by
    unfold tvcValue; have := hDpos 0; have := hP 0; positivity
  have hr0 : 0 ≤ β * μ / Pis := by positivity
  rw [show tvcValue β lam φ (fun _ => Pis) P D =
    fun T => tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T from funext hval]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hr1 : 1 ≤ β * μ / Pis := (one_le_div hPis).mpr hcon
    have hev : ∀ᶠ T in atTop, tvcValue β lam φ (fun _ => Pis) P D 0 ≤
        tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T :=
      Eventually.of_forall fun T => le_mul_of_one_le_right h0.le (one_le_pow₀ hr1)
    have := ge_of_tendsto h hev
    linarith
  · intro h
    have hr1 : β * μ / Pis < 1 := (div_lt_one hPis).mpr h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (tvcValue β lam φ (fun _ => Pis) P D 0)

end WoodfordMuBar

/-! ## The Schmitt-Grohé–Uribe example, restated from the Woodford Chapter 2 project -/

namespace SGU

open Cochrane.NewKeynesianSelection.SelectionPatches.WoodfordMuBar

/-! ## Preferences, (A.54) and (A.55) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: the optimal cash-goods purchases `c₁ = min(m, C/(1 + θ))`. -/
noncomputable def c1opt (θ C m : ℝ) : ℝ := min m (C / (1 + θ))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.53), p. 654: the indirect utility
`u(C, m) = log c₁ + θ log(C − c₁)` at the optimal `c₁`. -/
noncomputable def uSGU (θ C m : ℝ) : ℝ :=
  Real.log (c1opt θ C m) + θ * Real.log (C - c1opt θ C m)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.53), p. 654, "the optimal level of cash goods purchases is equal to
`c₁ = min(m, C/(1 + θ))`": for `θ, C, m > 0`, every feasible `c₁ ∈ (0, m]` with `c₁ < C` gives
`log c₁ + θ log(C − c₁) ≤ u(C, m)`. -/
theorem c1opt_optimal {θ C m c1 : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hm : 0 < m) (h0 : 0 < c1)
    (hc1m : c1 ≤ m) (hc1C : c1 < C) :
    Real.log c1 + θ * Real.log (C - c1) ≤ uSGU θ C m := by
  unfold uSGU
  set cs := c1opt θ C m with hcs
  have hθ1 : 0 < 1 + θ := by linarith
  have hcsle : cs ≤ C / (1 + θ) := min_le_right _ _
  have hcspos : 0 < cs := lt_min hm (div_pos hC hθ1)
  have hCcs : 0 < C - cs := by
    have : C / (1 + θ) < C := by rw [div_lt_iff₀ hθ1]; nlinarith
    linarith
  have h1 : Real.log c1 - Real.log cs ≤ c1 / cs - 1 := by
    rw [← Real.log_div h0.ne' hcspos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos h0 hcspos)
  have h2 : Real.log (C - c1) - Real.log (C - cs) ≤ (C - c1) / (C - cs) - 1 := by
    rw [← Real.log_div (by linarith) hCcs.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hCcs)
  have hkey : (c1 / cs - 1) + θ * ((C - c1) / (C - cs) - 1) ≤ 0 := by
    have e : (c1 / cs - 1) + θ * ((C - c1) / (C - cs) - 1) =
        (c1 - cs) * ((C - cs) - θ * cs) / (cs * (C - cs)) := by
      field_simp
      ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rcases le_total m (C / (1 + θ)) with hle | hle
    · have hcsm : cs = m := min_eq_left hle
      have hA : c1 - cs ≤ 0 := by rw [hcsm]; linarith
      have hB : 0 ≤ (C - cs) - θ * cs := by
        rw [hcsm]
        rw [le_div_iff₀ hθ1] at hle
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg hA hB
    · have hcsC : cs = C / (1 + θ) := min_eq_right hle
      have hB : (C - cs) - θ * cs = 0 := by rw [hcsC]; field_simp; ring
      rw [hB, mul_zero]
  nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.54), p. 654, region where the cash constraint binds
(`m < C/(1 + θ)`): `u_C = θ/(C − m)`, `u_m = 1/m − θ/(C − m)`, so
`λ = u_C + u_m = 1/m = 1/min(m, C/(1 + θ))`. -/
theorem lambda_A54_binding {θ C m : ℝ} (hθ : 0 < θ) (hm : 0 < m) (hmC : m < C / (1 + θ)) :
    HasDerivAt (fun C' => uSGU θ C' m) (θ / (C - m)) C ∧
      HasDerivAt (fun m' => uSGU θ C m') (1 / m - θ / (C - m)) m ∧
      θ / (C - m) + (1 / m - θ / (C - m)) = 1 / c1opt θ C m := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hmC' : m * (1 + θ) < C := by rwa [lt_div_iff₀ hθ1] at hmC
  have hCm : 0 < C - m := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h := ((hasDerivAt_id C).sub_const m).log hCm.ne'
    have h2 := (h.const_mul θ).const_add (Real.log m)
    simp only [id, one_div] at h2
    refine (h2.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hmC'] with C' hC'
    have : m ≤ C' / (1 + θ) := by rw [le_div_iff₀ hθ1]; exact (Set.mem_Ioi.mp hC').le
    simp only [uSGU, c1opt, min_eq_left this]
  · have h1 := (hasDerivAt_id m).log hm.ne'
    have h2 := (((hasDerivAt_id m).const_sub C).log hCm.ne').const_mul θ
    have h3 := h1.add h2
    simp only [id] at h3
    refine (h3.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hmC] with m' hm'
    simp only [uSGU, c1opt, min_eq_left (Set.mem_Iio.mp hm').le]
    rfl
  · simp only [c1opt, min_eq_left hmC.le]
    field_simp
    ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.54), p. 654, region beyond satiation (`m > C/(1 + θ)`):
`u_C = (1 + θ)/C`, `u_m = 0`, so `λ = (1 + θ)/C = 1/min(m, C/(1 + θ))`. -/
theorem lambda_A54_satiated {θ C m : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hmC : C / (1 + θ) < m) :
    HasDerivAt (fun C' => uSGU θ C' m) ((1 + θ) / C) C ∧
      HasDerivAt (fun m' => uSGU θ C m') 0 m ∧ (1 + θ) / C + 0 = 1 / c1opt θ C m := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hmC' : C < m * (1 + θ) := by rwa [div_lt_iff₀ hθ1] at hmC
  refine ⟨?_, ?_, ?_⟩
  · have ha : HasDerivAt (fun C' : ℝ => C' / (1 + θ)) (1 / (1 + θ)) C := by
      simpa using (hasDerivAt_id C).div_const (1 + θ)
    have hb : HasDerivAt (fun C' : ℝ => C' - C' / (1 + θ)) (1 - 1 / (1 + θ)) C :=
      (hasDerivAt_id C).sub ha
    have hpos1 : C / (1 + θ) ≠ 0 := (div_pos hC hθ1).ne'
    have hpos2 : C - C / (1 + θ) ≠ 0 := by
      have : C / (1 + θ) < C := by rw [div_lt_iff₀ hθ1]; nlinarith
      linarith
    have h := (ha.log hpos1).add ((hb.log hpos2).const_mul θ)
    have hθ0 : θ ≠ 0 := hθ.ne'
    have hC0 : C ≠ 0 := hC.ne'
    have e1 : (1 : ℝ) - 1 / (1 + θ) = θ / (1 + θ) := by field_simp; ring
    have e2 : C - C / (1 + θ) = C * θ / (1 + θ) := by field_simp; ring
    refine (h.congr_deriv (by rw [e1, e2]; field_simp)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hmC'] with C' hC'
    have : C' / (1 + θ) ≤ m := by rw [div_le_iff₀ hθ1]; exact (Set.mem_Iio.mp hC').le
    simp only [uSGU, c1opt, min_eq_right this]
    rfl
  · refine (hasDerivAt_const m (uSGU θ C m)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hmC] with m' hm'
    simp only [uSGU, c1opt, min_eq_right (Set.mem_Ioi.mp hm').le, min_eq_right hmC.le]
  · simp only [c1opt, min_eq_right hmC.le]
    field_simp
    ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.55), p. 654: the liquidity-preference function
`L(Y, i) = Y/(1 + θ(1 + i))`. -/
noncomputable def LSGU (θ Y i : ℝ) : ℝ := Y / (1 + θ * (1 + i))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.41) ⇒ (A.55), p. 654: with `i^m = 0`, (A.41) reads `u_m/u_C = i`
(`Timing.oddsRatio_oppCost_zero`). For `i > 0` the real balances `m = L(Y, i)` lie in the region
where the cash constraint binds, and there `u_m/u_C = i` holds iff `m = Y/(1 + θ(1 + i))`. -/
theorem money_demand_A55 {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 < i) :
    0 < LSGU θ Y i ∧ LSGU θ Y i < Y / (1 + θ) ∧
      ∀ m, 0 < m → m < Y / (1 + θ) →
        ((1 / m - θ / (Y - m)) / (θ / (Y - m)) = i ↔ m = LSGU θ Y i) := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  refine ⟨div_pos hY hd, ?_, fun m hm hmY => ?_⟩
  · unfold LSGU
    exact div_lt_div_of_pos_left hY hθ1 (by nlinarith)
  · have hmY' : m * (1 + θ) < Y := by rwa [lt_div_iff₀ hθ1] at hmY
    have hYm : 0 < Y - m := by nlinarith
    have e : (1 / m - θ / (Y - m)) / (θ / (Y - m)) = (Y - m) / (θ * m) - 1 := by
      field_simp
    rw [e, LSGU, eq_div_iff hd.ne', sub_eq_iff_eq_add, div_eq_iff (by positivity)]
    constructor <;> intro h <;> linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: `λ(i) = (1 + θ(1 + i))/Ȳ`. -/
noncomputable def lamSGU (θ Y i : ℝ) : ℝ := (1 + θ * (1 + i)) / Y

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654, "substituting (A.55) into (A.54) … `λ(i) = (1 + θ(1 + i))/Ȳ` for all
`i ≥ 0`". -/
theorem lambda_of_i {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    1 / c1opt θ Y (LSGU θ Y i) = lamSGU θ Y i := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  have hle : LSGU θ Y i ≤ Y / (1 + θ) := by
    unfold LSGU
    exact div_le_div_of_nonneg_left hY.le hθ1 (by nlinarith)
  rw [c1opt, min_eq_left hle, LSGU, lamSGU]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654, "it can be made unboundedly large in the case of a high enough
interest rate". -/
theorem lamSGU_tendsto_atTop {θ Y : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    Tendsto (lamSGU θ Y) atTop atTop := by
  unfold lamSGU
  refine Tendsto.atTop_div_const hY ?_
  exact tendsto_atTop_add_const_left _ 1
    (Tendsto.const_mul_atTop hθ (tendsto_atTop_add_const_left _ 1 tendsto_id))

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: the elasticity of `λ(i)` with respect to `1 + i`,
`(1 + i)λ'(i)/λ(i)` with `λ' = θ/Ȳ`. -/
noncomputable def elasticity (θ Y i : ℝ) : ℝ := (1 + i) * (θ / Y) / lamSGU θ Y i

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: `λ'(i) = θ/Ȳ`. -/
theorem hasDerivAt_lamSGU (θ Y i : ℝ) : HasDerivAt (lamSGU θ Y) (θ / Y) i := by
  have h := (((hasDerivAt_id i).const_add 1).const_mul θ).const_add 1
  exact (h.div_const Y).congr_deriv (by ring)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654 ("the elasticity of `λ(i)` with respect to `i` remains bounded below
1") and p. 137 (elasticity with respect to `1 + i` "positive, but bounded below one"): for
`i ≥ 0` the elasticity equals `θ(1 + i)/(1 + θ(1 + i)) ∈ (0, 1)`. -/
theorem elasticity_lt_one {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    elasticity θ Y i = θ * (1 + i) / (1 + θ * (1 + i)) ∧ 0 < elasticity θ Y i ∧
      elasticity θ Y i < 1 := by
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  have e : elasticity θ Y i = θ * (1 + i) / (1 + θ * (1 + i)) := by
    unfold elasticity lamSGU
    field_simp
  refine ⟨e, ?_, ?_⟩
  · rw [e]; have : 0 < 1 + i := by linarith
    positivity
  · rw [e, div_lt_one hd]; linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654, precision: the elasticity tends to `1` as `i → ∞`, so it is below one
at every `i` but admits no uniform bound `k < 1`. -/
theorem elasticity_tendsto_one {θ Y : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    Tendsto (elasticity θ Y) atTop (𝓝 1) := by
  have h1 : Tendsto (fun i : ℝ => θ * (1 + i)) atTop atTop :=
    Tendsto.const_mul_atTop hθ (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 : Tendsto (fun i : ℝ => 1 - 1 / (1 + θ * (1 + i))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 h1))
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with i hi
  rw [(elasticity_lt_one hθ hY hi).1]
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: the elasticity with respect to `i`, `iλ'(i)/λ(i) = θi/(1 + θ(1 + i))`,
is also below one for `i ≥ 0`. -/
theorem elasticity_i_lt_one {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    i * (θ / Y) / lamSGU θ Y i < 1 := by
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  unfold lamSGU
  rw [div_lt_one (by positivity)]
  rw [mul_div_assoc', div_lt_div_iff_of_pos_right hY]
  nlinarith

/-! ## The Taylor rule (A.56) -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56), p. 654: `1 + φ(Π) = β⁻¹[Π* + φ_π(Π − Π*)]` on its linear range. -/
noncomputable def ellSGU (β Pis φπ x : ℝ) : ℝ := (Pis + φπ * (x - Pis)) / β

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56) and fn. 8, p. 655: the rule
`φ(Π) = β⁻¹[Π* + φ_π(Π − Π*)] − 1`, truncated at zero ("this form holds … only for inflation
rates for which it implies a nonnegative interest rate"). -/
noncomputable def phiSGU (β Pis φπ x : ℝ) : ℝ := max 0 (ellSGU β Pis φπ x - 1)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56): `1 + φ(Π) = max(1, ℓ(Π))`. -/
theorem one_add_phiSGU (β Pis φπ x : ℝ) :
    1 + phiSGU β Pis φπ x = max 1 (ellSGU β Pis φπ x) := by
  unfold phiSGU
  rw [← max_add_add_left]
  simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56): `φ ≥ 0`. -/
theorem phiSGU_nonneg (β Pis φπ x : ℝ) : 0 ≤ phiSGU β Pis φπ x := le_max_left _ _

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56): the rule is continuous. -/
theorem phiSGU_continuous (β Pis φπ : ℝ) : Continuous (phiSGU β Pis φπ) := by
  unfold phiSGU ellSGU
  fun_prop

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (A.56), p. 655: the rule is "consistent with a steady-state inflation rate
`Π*`": `φ(Π*) = β⁻¹Π* − 1` when `Π* ≥ β`. -/
theorem phiSGU_target {β Pis φπ : ℝ} (hβ : 0 < β) (hPis : β ≤ Pis) :
    phiSGU β Pis φπ Pis = Pis / β - 1 := by
  unfold phiSGU ellSGU
  rw [sub_self, mul_zero, add_zero, max_eq_right]
  rw [sub_nonneg, le_div_iff₀ hβ]
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "such a rule satisfies the Taylor principle if and only if
`φ_π > 1`": for `Π* > β`, `φ'(Π*) = φ_π/β`, and the Taylor coefficient `Π*φ'(Π*)/(1 + φ(Π*))`
(= the slope `βφ'(Π*)` of the map (4.6), `GlobalDynamics.taylorCoeff_eq_slope`) equals `φ_π`. -/
theorem taylorCoeff_phiSGU {β Pis φπ : ℝ} (hβ : 0 < β) (hPis : β < Pis) :
    HasDerivAt (phiSGU β Pis φπ) (φπ / β) Pis ∧
      Pis * (φπ / β) / (1 + phiSGU β Pis φπ Pis) = φπ := by
  have hlin : HasDerivAt (fun x => ellSGU β Pis φπ x - 1) (φπ / β) Pis := by
    have h := ((((hasDerivAt_id Pis).sub_const Pis).const_mul φπ).const_add Pis).div_const β
    simpa [ellSGU] using h.sub_const 1
  have hval : 0 < ellSGU β Pis φπ Pis - 1 := by
    unfold ellSGU
    rw [sub_self, mul_zero, add_zero, sub_pos, one_lt_div hβ]
    exact hPis
  have hev : (phiSGU β Pis φπ) =ᶠ[𝓝 Pis] fun x => ellSGU β Pis φπ x - 1 := by
    have hc : ContinuousAt (fun x => ellSGU β Pis φπ x - 1) Pis := hlin.continuousAt
    filter_upwards [hc.eventually (lt_mem_nhds hval)] with x hx
    unfold phiSGU
    rw [max_eq_right hx.le]
  refine ⟨hlin.congr_of_eventuallyEq hev, ?_⟩
  rw [taylorCoeff_eq_slope hβ (by linarith) (phiSGU_target hβ hPis.le)]
  field_simp

/-! ## The functions `A` and `B` -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `A(Π) ≡ λ(φ(Π))/(1 + φ(Π))`. -/
noncomputable def sguA (θ Y β Pis φπ x : ℝ) : ℝ :=
  lamSGU θ Y (phiSGU β Pis φπ x) / (1 + phiSGU β Pis φπ x)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `B(Π) ≡ βλ(φ(Π))/Π`. -/
noncomputable def sguB (θ Y β Pis φπ x : ℝ) : ℝ := β * lamSGU θ Y (phiSGU β Pis φπ x) / x

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 (error E5): the constant `β + θΠ*(1 − φ_π)`, whose sign decides the
direction of monotonicity of `B`. -/
def sguC (θ β Pis φπ : ℝ) : ℝ := β + θ * Pis * (1 - φπ)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 654: `λ(φ(Π)) > 0`. -/
theorem lamSGU_phi_pos {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    0 < lamSGU θ Y (phiSGU β Pis φπ x) := by
  unfold lamSGU
  have := phiSGU_nonneg β Pis φπ x
  have : 0 < 1 + θ * (1 + phiSGU β Pis φπ x) := by nlinarith
  positivity

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), (4.5) ⇔ p. 655: for positive inflation rates, (4.5) is
`B(Π_{t+1}) = A(Π_t)`. -/
theorem eq45_iff_AB {θ Y β Pis φπ x x' : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hx' : 0 < x') :
    x' / lamSGU θ Y (phiSGU β Pis φπ x') =
        β * (1 + phiSGU β Pis φπ x) / lamSGU θ Y (phiSGU β Pis φπ x) ↔
      sguB θ Y β Pis φπ x' = sguA θ Y β Pis φπ x := by
  have h1 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := x) hθ hY
  have h2 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := x') hθ hY
  have h3 : 0 < 1 + phiSGU β Pis φπ x := by linarith [phiSGU_nonneg β Pis φπ x]
  unfold sguA sguB
  rw [div_eq_div_iff h2.ne' h1.ne', div_eq_div_iff hx'.ne' h3.ne']
  constructor <;> intro h <;> nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: in terms of `M = 1 + φ(Π) = max(1, ℓ(Π))`,
`A = (1 + θM)/(ȲM)` and `B = β(1 + θM)/(ȲΠ)`. -/
theorem sguAB_formula (θ Y β Pis φπ x : ℝ) :
    sguA θ Y β Pis φπ x = (1 + θ * max 1 (ellSGU β Pis φπ x)) / Y / max 1 (ellSGU β Pis φπ x) ∧
      sguB θ Y β Pis φπ x = β * ((1 + θ * max 1 (ellSGU β Pis φπ x)) / Y) / x := by
  unfold sguA sguB lamSGU
  rw [one_add_phiSGU]
  exact ⟨rfl, rfl⟩

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, with the factor `1/Ȳ` restored: on the linear range of the rule,
`B(Π) = [β + θΠ*(1 − φ_π)]/(ȲΠ) + θφ_π/Ȳ`. -/
theorem sguB_formula {θ Y β Pis φπ x : ℝ} (hβ : 0 < β) (hY : 0 < Y) (hx : 0 < x)
    (hl : 1 ≤ ellSGU β Pis φπ x) :
    sguB θ Y β Pis φπ x = sguC θ β Pis φπ / (Y * x) + θ * φπ / Y := by
  rw [(sguAB_formula θ Y β Pis φπ x).2, max_eq_right hl]
  unfold ellSGU sguC
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "`A(Π)` is a monotonically decreasing function of `Π`": for
`φ_π ≥ 0`. -/
theorem sguA_antitone {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 0 ≤ φπ) : Antitone (sguA θ Y β Pis φπ) := by
  intro a b hab
  have hM : max 1 (ellSGU β Pis φπ a) ≤ max 1 (ellSGU β Pis φπ b) := by
    refine max_le_max le_rfl ?_
    unfold ellSGU
    exact div_le_div_of_nonneg_right (by nlinarith) hβ.le
  have ha1 : 1 ≤ max 1 (ellSGU β Pis φπ a) := le_max_left _ _
  rw [(sguAB_formula θ Y β Pis φπ a).1, (sguAB_formula θ Y β Pis φπ b).1]
  set Ma := max 1 (ellSGU β Pis φπ a)
  set Mb := max 1 (ellSGU β Pis φπ b)
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hY (by linarith : (0 : ℝ) < Ma)]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "approaches the asymptotic value of `θ`" — with the factor `1/Ȳ`
the text omits: `A(Π) → θ/Ȳ` as `Π → ∞` (for `φ_π > 0`). -/
theorem sguA_tendsto {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : 0 < φπ) :
    Tendsto (sguA θ Y β Pis φπ) atTop (𝓝 (θ / Y)) := by
  have hl : Tendsto (ellSGU β Pis φπ) atTop atTop := by
    unfold ellSGU
    refine Tendsto.atTop_div_const hβ ?_
    exact tendsto_atTop_add_const_left _ Pis
      (Tendsto.const_mul_atTop hφπ (tendsto_atTop_add_const_right _ (-Pis) tendsto_id))
  have h1 : Tendsto (fun x => 1 / (Y * ellSGU β Pis φπ x) + θ / Y) atTop (𝓝 (0 + θ / Y)) :=
    (tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hY hl)).add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [hl.eventually (eventually_ge_atTop 1)] with x hx
  rw [(sguAB_formula θ Y β Pis φπ x).1, max_eq_right hx]
  field_simp

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, error E5: if `β + θΠ*(1 − φ_π) > 0`, `B` is strictly decreasing on
`(0, ∞)` (on both the linear and the truncated range of the rule). -/
theorem sguB_strictAntiOn {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hc : 0 < sguC θ β Pis φπ) : StrictAntiOn (sguB θ Y β Pis φπ) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  rw [(sguAB_formula θ Y β Pis φπ a).2, (sguAB_formula θ Y β Pis φπ b).2]
  set Ma := max 1 (ellSGU β Pis φπ a) with hMa
  set Mb := max 1 (ellSGU β Pis φπ b) with hMb
  have hMa1 : 1 ≤ Ma := le_max_left _ _
  have hMal : ellSGU β Pis φπ a ≤ Ma := le_max_right _ _
  have hid : ∀ x, β * (1 + θ * ellSGU β Pis φπ x) = sguC θ β Pis φπ + θ * φπ * x := by
    intro x; unfold ellSGU sguC; field_simp; ring
  rw [div_lt_div_iff₀ hb' ha']
  suffices key : β * (1 + θ * Mb) * a < β * (1 + θ * Ma) * b by
    have e1 : β * ((1 + θ * Mb) / Y) * a = (1 / Y) * (β * (1 + θ * Mb) * a) := by ring
    have e2 : β * ((1 + θ * Ma) / Y) * b = (1 / Y) * (β * (1 + θ * Ma) * b) := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left key (by positivity)
  rcases le_total 1 (ellSGU β Pis φπ b) with hl | hl
  · have hMbe : Mb = ellSGU β Pis φπ b := max_eq_right hl
    rw [hMbe, hid b]
    have h1 : β * (1 + θ * ellSGU β Pis φπ a) ≤ β * (1 + θ * Ma) := by
      have := mul_le_mul_of_nonneg_left hMal hθ.le; nlinarith
    rw [hid a] at h1
    nlinarith [mul_lt_mul_of_pos_left hab hc]
  · have hMbe : Mb = 1 := max_eq_left hl
    rw [hMbe]
    have h1 : β * (1 + θ * 1) ≤ β * (1 + θ * Ma) := by
      have := mul_le_mul_of_nonneg_left hMa1 hθ.le; nlinarith
    have h2 : 0 < β * (1 + θ * 1) := by positivity
    nlinarith [mul_lt_mul_of_pos_left hab h2]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 (error E5): if `β + θΠ*(1 − φ_π) > 0` then `B(Π) > θφ_π/Ȳ` for every
`Π > 0` ("approaches the asymptotic value `φ_πθ`" from above). -/
theorem sguB_gt {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) (hx : 0 < x)
    (hc : 0 < sguC θ β Pis φπ) : θ * φπ / Y < sguB θ Y β Pis φπ x := by
  rw [(sguAB_formula θ Y β Pis φπ x).2]
  have hle : ellSGU β Pis φπ x ≤ max 1 (ellSGU β Pis φπ x) := le_max_right _ _
  have hid : β * (1 + θ * ellSGU β Pis φπ x) = sguC θ β Pis φπ + θ * φπ * x := by
    unfold ellSGU sguC; field_simp; ring
  rw [lt_div_iff₀ hx, div_mul_eq_mul_div, mul_div_assoc', div_lt_div_iff_of_pos_right hY]
  have : β * (1 + θ * ellSGU β Pis φπ x) ≤ β * (1 + θ * max 1 (ellSGU β Pis φπ x)) := by
    have := mul_le_mul_of_nonneg_left hle hθ.le; nlinarith
  nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `B(Π) → θφ_π/Ȳ` as `Π → ∞` (for `φ_π > 0`). -/
theorem sguB_tendsto {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : 0 < φπ) :
    Tendsto (sguB θ Y β Pis φπ) atTop (𝓝 (θ * φπ / Y)) := by
  have hl : Tendsto (ellSGU β Pis φπ) atTop atTop := by
    unfold ellSGU
    refine Tendsto.atTop_div_const hβ ?_
    exact tendsto_atTop_add_const_left _ Pis
      (Tendsto.const_mul_atTop hφπ (tendsto_atTop_add_const_right _ (-Pis) tendsto_id))
  have h1 : Tendsto (fun x => sguC θ β Pis φπ / (Y * x) + θ * φπ / Y) atTop
      (𝓝 (0 + θ * φπ / Y)) :=
    (tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hY tendsto_id)).add
      tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [hl.eventually (eventually_ge_atTop 1), eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  rw [sguB_formula hβ hY hx0 hx]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 (and the E6 condition of §4.1): if `φ_π > 1` and `Π* > β`, then
`A(Π) < B(Π)` for every `Π > Π*` — the curve (4.5) lies above the diagonal above the target. -/
theorem sguA_lt_B_above {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hx : Pis < x) :
    sguA θ Y β Pis φπ x < sguB θ Y β Pis φπ x := by
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ ellSGU β Pis φπ x := by
    unfold ellSGU; rw [le_div_iff₀ hβ]; nlinarith
  have hl0 : 0 < ellSGU β Pis φπ x := by linarith
  rw [(sguAB_formula θ Y β Pis φπ x).1, (sguAB_formula θ Y β Pis φπ x).2, max_eq_right hl]
  have hkey : x < β * ellSGU β Pis φπ x := by
    unfold ellSGU; field_simp; nlinarith
  have hp : 0 < (1 + θ * ellSGU β Pis φπ x) / Y := by positivity
  rw [div_lt_div_iff₀ hl0 hx0]
  nlinarith [mul_lt_mul_of_pos_left hkey hp]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: if `φ_π > 1` and `Π* > β`, then `B(Π) < A(Π)` for `β < Π < Π*`. -/
theorem sguB_lt_A_below {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hx1 : β < x) (hx2 : x < Pis) :
    sguB θ Y β Pis φπ x < sguA θ Y β Pis φπ x := by
  have hx0 : 0 < x := by linarith
  rw [(sguAB_formula θ Y β Pis φπ x).1, (sguAB_formula θ Y β Pis φπ x).2]
  rcases le_total 1 (ellSGU β Pis φπ x) with hl | hl
  · rw [max_eq_right hl]
    have hl0 : 0 < ellSGU β Pis φπ x := by linarith
    have hkey : β * ellSGU β Pis φπ x < x := by
      unfold ellSGU; field_simp; nlinarith
    have hp : 0 < (1 + θ * ellSGU β Pis φπ x) / Y := by positivity
    rw [div_lt_div_iff₀ hx0 hl0]
    nlinarith [mul_lt_mul_of_pos_left hkey hp]
  · rw [max_eq_left hl, div_one, div_lt_iff₀ hx0]
    have hp : 0 < (1 + θ * 1) / Y := by positivity
    nlinarith [mul_lt_mul_of_pos_left hx1 hp]

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `ℓ(β) < 1` (so `φ(β) = 0` and `Π** = β`) when `φ_π > 1`, `Π* > β`;
hence `A(Π) = (1 + θ)/Ȳ = B(β)` for all `Π ≤ β`, and `A ≤ (1 + θ)/Ȳ` everywhere. -/
theorem sgu_at_beta {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) (hφπ : 1 < φπ)
    (hPis : β < Pis) :
    ellSGU β Pis φπ β < 1 ∧ phiSGU β Pis φπ β = 0 ∧ sguB θ Y β Pis φπ β = (1 + θ) / Y ∧
      (∀ x, x ≤ β → sguA θ Y β Pis φπ x = (1 + θ) / Y) ∧
      ∀ x, sguA θ Y β Pis φπ x ≤ (1 + θ) / Y := by
  have hlβ : ellSGU β Pis φπ β < 1 := by
    unfold ellSGU; rw [div_lt_one hβ]; nlinarith
  have hmono : ∀ x, x ≤ β → ellSGU β Pis φπ x ≤ ellSGU β Pis φπ β := fun x hx => by
    unfold ellSGU; exact div_le_div_of_nonneg_right (by nlinarith) hβ.le
  refine ⟨hlβ, ?_, ?_, fun x hx => ?_, fun x => ?_⟩
  · unfold phiSGU; exact max_eq_left (by linarith)
  · rw [(sguAB_formula θ Y β Pis φπ β).2, max_eq_left hlβ.le]
    field_simp
  · rw [(sguAB_formula θ Y β Pis φπ x).1, max_eq_left (le_trans (hmono x hx) hlβ.le)]
    simp
  · rw [(sguAB_formula θ Y β Pis φπ x).1]
    have hM : 1 ≤ max 1 (ellSGU β Pis φπ x) := le_max_left _ _
    rw [div_div, div_le_div_iff₀ (by positivity) hY]
    nlinarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: the bound `Π̄`, defined by `1 + φ(Π̄) = 1/(θ(φ_π − 1))`. -/
noncomputable def sguPibar (θ β Pis φπ : ℝ) : ℝ := Pis + (β / (θ * (φπ - 1)) - Pis) / φπ

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "there exists a finite `Π̄` such that `A(Π̄) = φ_πθ`" (with `1/Ȳ`):
under `φ_π > 1`, `Π* > β` and the E5 hypothesis `β + θΠ*(1 − φ_π) > 0`, `Π̄ > Π*`, and
`A(Π̄) = θφ_π/Ȳ`. -/
theorem sguPibar_spec {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ) :
    Pis < sguPibar θ β Pis φπ ∧ ellSGU β Pis φπ (sguPibar θ β Pis φπ) = 1 / (θ * (φπ - 1)) ∧
      sguA θ Y β Pis φπ (sguPibar θ β Pis φπ) = θ * φπ / Y := by
  have hk : 0 < θ * (φπ - 1) := by nlinarith
  have hφ0 : 0 < φπ := by linarith
  have hk1 : φπ - 1 ≠ 0 := by linarith
  have hkP : θ * (φπ - 1) * Pis < β := by unfold sguC at hc; nlinarith
  have hgt : Pis < β / (θ * (φπ - 1)) := by rw [lt_div_iff₀ hk]; linarith
  have hell : ellSGU β Pis φπ (sguPibar θ β Pis φπ) = 1 / (θ * (φπ - 1)) := by
    unfold ellSGU sguPibar
    field_simp
    ring
  have hPi : Pis < sguPibar θ β Pis φπ := by
    unfold sguPibar
    have : 0 < (β / (θ * (φπ - 1)) - Pis) / φπ := div_pos (by linarith) hφ0
    linarith
  refine ⟨hPi, hell, ?_⟩
  have h1 : 1 ≤ 1 / (θ * (φπ - 1)) := by
    rw [le_div_iff₀ hk, one_mul]
    have : Pis / β > 1 := (one_lt_div hβ).mpr hPis
    have h2 : θ * (φπ - 1) * Pis < β := hkP
    nlinarith
  rw [(sguAB_formula θ Y β Pis φπ _).1, hell, max_eq_right h1]
  field_simp
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "in the case of any `Π_t ≥ Π̄`, there is no value for `Π_{t+1}` that
would satisfy (4.5)" — true under the E5 hypothesis. -/
theorem sgu_no_successor {θ Y β Pis φπ x x' : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hx : sguPibar θ β Pis φπ ≤ x) (hx' : 0 < x') :
    sguB θ Y β Pis φπ x' ≠ sguA θ Y β Pis φπ x := by
  have h1 := sguA_antitone (θ := θ) (Pis := Pis) hY hβ (by linarith : (0 : ℝ) ≤ φπ) hx
  rw [(sguPibar_spec hθ hY hβ hφπ hPis hc).2.2] at h1
  have h2 := sguB_gt hθ hY hβ hx' hc (Pis := Pis) (φπ := φπ)
  intro h
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655: `A` and `B` are continuous at every `Π > 0`. -/
theorem sguAB_continuousAt {θ Y β Pis φπ x : ℝ} (hY : 0 < Y) (hx : 0 < x) :
    ContinuousAt (sguA θ Y β Pis φπ) x ∧ ContinuousAt (sguB θ Y β Pis φπ) x := by
  have hφ := (phiSGU_continuous β Pis φπ).continuousAt (x := x)
  have hl : ContinuousAt (fun z => lamSGU θ Y (phiSGU β Pis φπ z)) x := by
    unfold lamSGU
    exact ((continuousAt_const.add (continuousAt_const.mul (continuousAt_const.add hφ)))).div
      continuousAt_const hY.ne'
  refine ⟨hl.div (continuousAt_const.add hφ) (by linarith [phiSGU_nonneg β Pis φπ x]), ?_⟩
  exact (continuousAt_const.mul hl).div continuousAt_id hx.ne'

/-! ## Exclusion of self-fulfilling inflations and deflations -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "it is not possible to have a perfect-foresight equilibrium sequence
… in which `Π_t > Π*` in any period", under the added E5 hypothesis
`β + θΠ*(1 − φ_π) > 0` (with `φ_π > 1`, `Π* > β`): every solution of (4.5) satisfies `Π_t ≤ Π*`
at all dates. (Proof: above `Π*` the path must rise — `B > A` there and `B` is decreasing —
while `B > θφ_π/Ȳ` keeps it below `Π̄`; a bounded increasing path would converge to a steady
state above `Π*`, which does not exist.) -/
theorem sgu_no_hyperinflation {θ Y β Pis φπ : ℝ} {Pi_ : ℕ → ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) : ∀ t, Pi_ t ≤ Pis := by
  intro t0
  by_contra hcon
  push Not at hcon
  have hAB : ∀ t, sguB θ Y β Pis φπ (Pi_ (t + 1)) = sguA θ Y β Pis φπ (Pi_ t) := fun t =>
    (eq45_iff_AB hθ hY (hpath.1 (t + 1))).mp (hpath.2 t)
  have hsa := sguB_strictAntiOn (Y := Y) hθ hY hβ hc
  set y : ℕ → ℝ := fun n => Pi_ (n + t0) with hy
  have hyAB : ∀ n, sguB θ Y β Pis φπ (y (n + 1)) = sguA θ Y β Pis φπ (y n) := fun n => by
    simp only [hy, show n + 1 + t0 = n + t0 + 1 by omega]; exact hAB _
  have hypos : ∀ n, 0 < y n := fun n => hpath.1 _
  have hstep : ∀ n, Pis < y n ∧ y n < y (n + 1) := by
    intro n
    induction n with
    | zero =>
      have h0 : Pis < y 0 := by simp only [hy, zero_add]; exact hcon
      refine ⟨h0, ?_⟩
      by_contra hle
      push Not at hle
      have h1 := hsa.antitoneOn (hypos 1) (hypos 0) hle
      have h2 := sguA_lt_B_above hθ hY hβ hφπ hPis h0 (Y := Y)
      rw [hyAB 0] at h1
      linarith
    | succ n ih =>
      have h0 : Pis < y (n + 1) := by linarith [ih.1, ih.2]
      refine ⟨h0, ?_⟩
      by_contra hle
      push Not at hle
      have h1 := hsa.antitoneOn (hypos _) (hypos _) hle
      have h2 := sguA_lt_B_above hθ hY hβ hφπ hPis h0 (Y := Y)
      rw [hyAB (n + 1)] at h1
      linarith
  have hmono : Monotone y := monotone_nat_of_le_succ fun n => (hstep n).2.le
  have hbdd : BddAbove (Set.range y) := by
    refine ⟨sguPibar θ β Pis φπ, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_contra hgt
    push Not at hgt
    exact sgu_no_successor hθ hY hβ hφπ hPis hc hgt.le (hypos (n + 1)) (hyAB n)
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ n, y n with hL
  have hL0 : y 0 ≤ L := le_ciSup hbdd 0
  have hLpos : 0 < L := by linarith [hypos 0]
  have hcont := sguAB_continuousAt (θ := θ) (β := β) (Pis := Pis) (φπ := φπ) hY hLpos
  have h1 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguB θ Y β Pis φπ L)) :=
    hcont.2.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguA θ Y β Pis φπ L)) := by
    simp only [hyAB]; exact hcont.1.tendsto.comp hlim
  have heq := tendsto_nhds_unique h1 h2
  have := sguA_lt_B_above hθ hY hβ hφπ hPis (by linarith [(hstep 0).1] : Pis < L) (Y := Y)
  linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655 and §4.2: under the hypotheses of `sgu_no_hyperinflation`, a
perfect-foresight path that is ever below `Π*` converges to the Friedman rate `Π** = β`. -/
theorem sgu_deflation_tendsto {θ Y β Pis φπ : ℝ} {Pi_ : ℕ → ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) {t0 : ℕ} (ht0 : Pi_ t0 < Pis) :
    Tendsto Pi_ atTop (𝓝 β) := by
  have hAB : ∀ t, sguB θ Y β Pis φπ (Pi_ (t + 1)) = sguA θ Y β Pis φπ (Pi_ t) := fun t =>
    (eq45_iff_AB hθ hY (hpath.1 (t + 1))).mp (hpath.2 t)
  have hsa := sguB_strictAntiOn (Y := Y) hθ hY hβ hc
  obtain ⟨-, -, hBβ, hAle, hAmax⟩ := sgu_at_beta (Y := Y) hθ hY hβ hφπ hPis
  -- the successor of any `Π < Π*` lies in `[β, max(Π, β)]`, strictly below `Π` if `Π > β`
  have hsucc : ∀ x x', 0 < x → x < Pis → 0 < x' →
      sguB θ Y β Pis φπ x' = sguA θ Y β Pis φπ x → β ≤ x' ∧ (x ≤ β → x' = β) ∧
        (β < x → x' < x) := by
    intro x x' hx hxP hx' hBA
    have hlow : β ≤ x' := by
      by_contra hlt
      push Not at hlt
      have := hsa hx' hβ hlt
      rw [hBA, hBβ] at this
      linarith [hAmax x]
    refine ⟨hlow, fun hxβ => ?_, fun hxβ => ?_⟩
    · rw [hAle x hxβ, ← hBβ] at hBA
      exact hsa.injOn hx' hβ hBA
    · by_contra hge
      push Not at hge
      have h1 := hsa.antitoneOn hx hx' hge
      have h2 := sguB_lt_A_below (Y := Y) hθ hY hβ hφπ hxβ hxP
      rw [hBA] at h1
      linarith
  set y : ℕ → ℝ := fun n => Pi_ (n + (t0 + 1)) with hy
  have hyAB : ∀ n, sguB θ Y β Pis φπ (y (n + 1)) = sguA θ Y β Pis φπ (y n) := fun n => by
    simp only [hy, show n + 1 + (t0 + 1) = n + (t0 + 1) + 1 by omega]; exact hAB _
  have hypos : ∀ n, 0 < y n := fun n => hpath.1 _
  have hy0 : β ≤ y 0 ∧ y 0 < Pis := by
    have h := hsucc _ _ (hpath.1 t0) ht0 (hpath.1 (t0 + 1)) (hAB t0)
    simp only [hy, zero_add]
    refine ⟨h.1, ?_⟩
    rcases le_or_gt (Pi_ t0) β with hle | hlt
    · rw [h.2.1 hle]; exact hPis
    · exact lt_trans (h.2.2 hlt) ht0
  have hstep : ∀ n, (β ≤ y n ∧ y n < Pis) ∧ y (n + 1) ≤ y n := by
    intro n
    induction n with
    | zero =>
      refine ⟨hy0, ?_⟩
      have h := hsucc _ _ (hypos 0) hy0.2 (hypos 1) (hyAB 0)
      rcases hy0.1.lt_or_eq with hlt | heq
      · exact (h.2.2 hlt).le
      · rw [h.2.1 heq.symm.le, heq]
    | succ n ih =>
      have h := hsucc _ _ (hypos n) ih.1.2 (hypos (n + 1)) (hyAB n)
      have hmem : β ≤ y (n + 1) ∧ y (n + 1) < Pis := ⟨h.1, lt_of_le_of_lt ih.2 ih.1.2⟩
      refine ⟨hmem, ?_⟩
      have h' := hsucc _ _ (hypos (n + 1)) hmem.2 (hypos (n + 2)) (hyAB (n + 1))
      rcases hmem.1.lt_or_eq with hlt | heq
      · exact (h'.2.2 hlt).le
      · rw [h'.2.1 heq.symm.le, heq]
  have hanti : Antitone y := antitone_nat_of_succ_le fun n => (hstep n).2
  have hbdd : BddBelow (Set.range y) := ⟨β, by rintro _ ⟨n, rfl⟩; exact (hstep n).1.1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, y n with hL
  have hLβ : β ≤ L := le_ciInf fun n => (hstep n).1.1
  have hLP : L < Pis := lt_of_le_of_lt (ciInf_le hbdd 0) (hstep 0).1.2
  have hcont := sguAB_continuousAt (θ := θ) (β := β) (Pis := Pis) (φπ := φπ) hY
    (by linarith : 0 < L) (Y := Y)
  have h1 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguB θ Y β Pis φπ L)) :=
    hcont.2.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguA θ Y β Pis φπ L)) := by
    simp only [hyAB]; exact hcont.1.tendsto.comp hlim
  have heq := tendsto_nhds_unique h1 h2
  have hLeq : L = β := by
    rcases hLβ.lt_or_eq with hlt | heq'
    · have := sguB_lt_A_below (Y := Y) hθ hY hβ hφπ hlt hLP
      linarith
    · exact heq'.symm
  rw [hLeq] at hlim
  exact (tendsto_add_atTop_iff_nat (t0 + 1)).mp hlim

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), p. 655, "Schmitt-Grohé and Uribe establish that in the case of an
interest-rate rule satisfying the Taylor principle and a balanced-budget fiscal rule, the unique
perfect-foresight equilibrium is the one in which `Π_t = Π*` at all times", under the added E5
hypothesis `β + θΠ*(1 − φ_π) > 0`: with nominal liabilities growing at `μ̄`, `1 < μ̄ < Π*/β`,
the constant path `Π*` solves (4.5) and satisfies the transversality condition (1.24), and a
solution of (4.5) satisfies (1.24) iff it is that constant path. -/
theorem sgu_unique_pf_equilibrium {θ Y β Pis φπ μ : ℝ} {Pi_ P D : ℕ → ℝ} (hθ : 0 < θ)
    (hY : 0 < Y) (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hμ : 1 < μ) (hμPis : β * μ < Pis)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) (fun _ => Pis) ∧
      (Tendsto (tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_ P D) atTop (𝓝 0) ↔
        ∀ t, Pi_ t = Pis) := by
  have htarget : 1 + phiSGU β Pis φπ Pis = Pis / β := by
    rw [phiSGU_target hβ hPis.le]; ring
  have hconst : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) (fun _ => Pis) :=
    ⟨fun _ => by linarith, fun _ => by
      rw [htarget]; field_simp⟩
  refine ⟨hconst, ⟨fun htvc t => ?_, fun hall => ?_⟩⟩
  · have hle := sgu_no_hyperinflation hθ hY hβ hφπ hPis hc hpath t
    by_contra hne
    have hlt : Pi_ t < Pis := lt_of_le_of_ne hle hne
    have hlim := sgu_deflation_tendsto hθ hY hβ hφπ hPis hc hpath hlt
    obtain ⟨-, hφβ, -, -, -⟩ := sgu_at_beta (Y := Y) hθ hY hβ hφπ hPis
    exact deflation_tvc_violated hβ hpath (fun s => lamSGU_phi_pos hθ hY)
      (fun s => phiSGU_nonneg _ _ _ _) hP hPrec hD hDpos hlim
      (phiSGU_continuous β Pis φπ).continuousAt (by rw [hφβ, div_self hβ.ne']; ring)
      (by rw [div_self hβ.ne']; exact hμ) htvc
  · have hPi : Pi_ = fun _ => Pis := funext hall
    subst hPi
    exact (target_tvc_iff hβ (by linarith) (by linarith) htarget (lamSGU_phi_pos hθ hY) hP
      hPrec hD hDpos).mpr hμPis

/-! ## Error E5: a counterexample when `β + θΠ*(1 − φ_π) < 0` -/

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: the successor map on the upper branch of (4.5) in the
counterexample `β = 1/2, θ = 1, φ_π = 3/2, Π* = 3, Ȳ = 1`: `Π ↦ (6Π − 6)/(3Π − 5)`. -/
noncomputable def gE5 (x : ℝ) : ℝ := (6 * x - 6) / (3 * x - 5)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: the price level `P_t = ∏_{s<t} Π_{s+1}` (with `P₀ = 1`). -/
def priceFrom (Pi_ : ℕ → ℝ) (t : ℕ) : ℝ := ∏ s ∈ Finset.range t, Pi_ (s + 1)

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: in the counterexample, `φ(Π) = 3Π − 4` for `Π ≥ 4/3`. -/
theorem phiE5 {x : ℝ} (hx : 4 / 3 ≤ x) : phiSGU (1 / 2) 3 (3 / 2) x = 3 * x - 4 := by
  unfold phiSGU ellSGU
  rw [max_eq_right (by linarith)]
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: the interval `[32/13, 4]` is invariant under the upper
branch map. -/
theorem gE5_mem {x : ℝ} (h1 : 32 / 13 ≤ x) (h2 : x ≤ 4) : 32 / 13 ≤ gE5 x ∧ gE5 x ≤ 4 := by
  unfold gE5
  have hd : 0 < 3 * x - 5 := by linarith
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, error E5: on `[32/13, 4]` the upper branch map solves (4.5). -/
theorem gE5_eq45 {x : ℝ} (h1 : 32 / 13 ≤ x) (h2 : x ≤ 4) :
    gE5 x / lamSGU 1 1 (phiSGU (1 / 2) 3 (3 / 2) (gE5 x)) =
      1 / 2 * (1 + phiSGU (1 / 2) 3 (3 / 2) x) / lamSGU 1 1 (phiSGU (1 / 2) 3 (3 / 2) x) := by
  have hg := gE5_mem h1 h2
  rw [phiE5 (by linarith), phiE5 (by linarith [hg.1])]
  unfold lamSGU gE5
  have hd : 0 < 3 * x - 5 := by linarith
  have e1 : (1 + 1 * (1 + (3 * ((6 * x - 6) / (3 * x - 5)) - 4))) / 1 =
      (12 * x - 8) / (3 * x - 5) := by
    field_simp; ring
  have e2 : (1 + 1 * (1 + (3 * x - 4))) / 1 = 3 * x - 2 := by ring
  rw [e1, e2, div_div_div_cancel_right₀ hd.ne', div_eq_div_iff (by linarith) (by linarith)]
  ring

/-- Restated from the Woodford Chapter 2 project (used for Cochrane (2023), §16.10.6).
Woodford (2003), A.17, p. 655, error E5 — counterexample. Take `β = 1/2`, `θ = 1`,
`φ_π = 3/2 > 1` (Taylor principle), `Π* = 3`, `Ȳ = 1`; then `β + θΠ*(1 − φ_π) = −1 < 0`, and:
(i) the printed bound `Π̄` (`A(Π̄) = θφ_π/Ȳ`) is `5/3 < Π*`; (ii) `B` is not decreasing
(`B(3) < B(4)`); (iii) contrary to "in the case of any `Π_t ≥ Π̄` there is no value for `Π_{t+1}`
that would satisfy (4.5)", `Π_t = 4` has the successor `18/7`; (iv) with nominal liabilities
`D_t = 2^t` (`μ̄ = 2 ∈ (1, Π*/β)`) and `P_t = ∏_{s<t}Π_{s+1}`, both `Π_t ≡ 3` and the path
`Π_0 = 4`, `Π_{t+1} = (6Π_t − 6)/(3Π_t − 5)` solve (4.5), satisfy (4.4) (with
`L(i) = Ȳ/(1 + θ(1 + i))`) and satisfy the transversality condition (1.24): the
perfect-foresight equilibrium is not unique, and `Π_0 = 4 > Π*` refutes "`Π_t ≤ Π*` at all
times". -/
theorem e5_counterexample :
    sguC 1 (1 / 2) 3 (3 / 2) = -1 ∧
      (sguA 1 1 (1 / 2) 3 (3 / 2) (5 / 3) = 1 * (3 / 2) / 1 ∧ (5 / 3 : ℝ) < 3) ∧
      sguB 1 1 (1 / 2) 3 (3 / 2) 3 < sguB 1 1 (1 / 2) 3 (3 / 2) 4 ∧
      sguB 1 1 (1 / 2) 3 (3 / 2) (18 / 7) = sguA 1 1 (1 / 2) 3 (3 / 2) 4 ∧
      (IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) (fun _ => 3) ∧
        Tendsto (tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) (fun _ => 3)
          (priceFrom fun _ => 3) (fun t => 2 ^ t)) atTop (𝓝 0)) ∧
      ∃ Pi_ : ℕ → ℝ, Pi_ 0 = 4 ∧ IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ ∧
        Summable (bound44Term (1 / 2) 1 (lamSGU 1 1) (LSGU 1 1)
          (fun t => phiSGU (1 / 2) 3 (3 / 2) (Pi_ t))) ∧
        Tendsto (tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ (priceFrom Pi_)
          (fun t => 2 ^ t)) atTop (𝓝 0) := by
  have hφ3 : phiSGU (1 / 2) 3 (3 / 2) 3 = 5 := by rw [phiE5 (by norm_num)]; norm_num
  have hφ4 : phiSGU (1 / 2) 3 (3 / 2) 4 = 8 := by rw [phiE5 (by norm_num)]; norm_num
  refine ⟨by unfold sguC; norm_num, ⟨?_, by norm_num⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · unfold sguA lamSGU; rw [phiE5 (by norm_num)]; norm_num
  · unfold sguB lamSGU; rw [hφ3, hφ4]; norm_num
  · unfold sguA sguB lamSGU; rw [phiE5 (by norm_num), hφ4]; norm_num
  · exact ⟨fun _ => by norm_num, fun _ => by unfold lamSGU; rw [hφ3]; norm_num⟩
  · refine (target_tvc_iff (μ := 2) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hφ3]; norm_num)
      (by unfold lamSGU; rw [hφ3]; norm_num) (fun t => by unfold priceFrom; positivity)
      (fun t => by unfold priceFrom; rw [Finset.prod_range_succ, mul_comm])
      (fun t => by show (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t; ring) (fun t => by positivity)).mpr
      (by norm_num)
  · set Pi_ : ℕ → ℝ := fun t => gE5^[t] 4 with hPi
    have hsucc : ∀ t, Pi_ (t + 1) = gE5 (Pi_ t) := fun t => Function.iterate_succ_apply' _ _ _
    have hmem : ∀ t, 32 / 13 ≤ Pi_ t ∧ Pi_ t ≤ 4 := by
      intro t
      induction t with
      | zero => simp only [hPi, Function.iterate_zero, id]; norm_num
      | succ n ih => rw [hsucc]; exact gE5_mem ih.1 ih.2
    have hpos : ∀ t, 0 < Pi_ t := fun t => by linarith [(hmem t).1]
    have hpath : IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ :=
      ⟨hpos, fun t => by rw [hsucc]; exact gE5_eq45 (hmem t).1 (hmem t).2⟩
    have hφ : ∀ t, phiSGU (1 / 2) 3 (3 / 2) (Pi_ t) = 3 * Pi_ t - 4 := fun t =>
      phiE5 (by linarith [(hmem t).1])
    refine ⟨Pi_, rfl, hpath, ?_, ?_⟩
    · refine (bound44_summable (β := 1 / 2) (ybar := 1) (Λ := 10) (K := 1) (by norm_num)
        (by norm_num) (by norm_num)
        (fun T => phiSGU_nonneg _ _ _ _) (fun T => lamSGU_phi_pos one_pos one_pos)
        (fun T => ?_) (fun j hj => ?_) (fun j hj => ?_)).2
      · unfold lamSGU; rw [hφ T]; linarith [(hmem T).2]
      · unfold LSGU; positivity
      · unfold LSGU
        rw [mul_div_assoc', div_le_one (by linarith)]
        linarith
    · have hP : ∀ t, 0 < priceFrom Pi_ t := fun t =>
        Finset.prod_pos fun s _ => hpos (s + 1)
      have hPrec : ∀ t, priceFrom Pi_ (t + 1) = Pi_ (t + 1) * priceFrom Pi_ t := fun t => by
        unfold priceFrom; rw [Finset.prod_range_succ, mul_comm]
      have hD : ∀ t, (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t := fun t => by ring
      set V := tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ (priceFrom Pi_)
        (fun t => 2 ^ t) with hV
      have hVsucc : ∀ T, V (T + 1) = V T * (2 / (1 + phiSGU (1 / 2) 3 (3 / 2) (Pi_ T))) :=
        tvcValue_succ (by norm_num) hpath (fun t => lamSGU_phi_pos one_pos one_pos)
          (fun t => by linarith [phiSGU_nonneg (1 / 2) 3 (3 / 2) (Pi_ t)]) hP hPrec hD
      have hV0 : ∀ T, 0 ≤ V T := fun T => by
        simp only [hV, tvcValue]
        have := lamSGU_phi_pos (β := 1 / 2) (Pis := 3) (φπ := 3 / 2) (x := Pi_ T)
          one_pos one_pos
        have := hP T
        positivity
      have hVle : ∀ T, V T ≤ V 0 * (26 / 57) ^ T := by
        intro T
        induction T with
        | zero => simp
        | succ n ih =>
          rw [hVsucc, hφ n, pow_succ]
          have h1 : 2 / (1 + (3 * Pi_ n - 4)) ≤ 26 / 57 := by
            rw [div_le_div_iff₀ (by linarith [(hmem n).1]) (by norm_num)]
            linarith [(hmem n).1]
          have h2 : 0 ≤ 2 / (1 + (3 * Pi_ n - 4)) := div_nonneg (by norm_num)
            (by linarith [(hmem n).1])
          calc V n * (2 / (1 + (3 * Pi_ n - 4))) ≤ V 0 * (26 / 57) ^ n * (2 / (1 + (3 * Pi_ n - 4)))
                := mul_le_mul_of_nonneg_right ih h2
            _ ≤ V 0 * (26 / 57) ^ n * (26 / 57) :=
                mul_le_mul_of_nonneg_left h1 (mul_nonneg (hV0 0) (by positivity))
            _ = V 0 * ((26 / 57) ^ n * (26 / 57)) := by ring
      have hlim : Tendsto (fun T => V 0 * (26 / 57 : ℝ) ^ T) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 26 / 57)
          (by norm_num)).const_mul (V 0)
      exact squeeze_zero hV0 hVle hlim

end SGU

/-! ## (16.31)–(16.32): residual money demand -/

/-- Cochrane (2023), eqs. (16.31)–(16.32), p. 393: with the rule `1 + i_t = Φ(Π_t)/β` and money
demand `M_t/P_t = L(y, i_t)`, write `k(Π) = u_c[y, L(y, Φ(Π)/β − 1)]` for the marginal utility at
the rule's interest rate. Then the intertemporal condition (16.31)
`1 + i_t = Π_{t+1}u_c(t)/(βu_c(t+1))` is equivalent to (16.32)
`Π_{t+1} = Φ(Π_t) k(Π_{t+1})/k(Π_t)`. (The book writes `L(y, Φ(Π))`; the argument of `L` is the
interest rate, `Φ(Π)/β − 1`.) -/
theorem eq1632_iff {β x x' : ℝ} {Φ k : ℝ → ℝ} (hβ : 0 < β) (hk : 0 < k x) (hk' : 0 < k x') :
    Φ x / β = x' * k x / (β * k x') ↔ x' = Φ x * k x' / k x := by
  generalize k x = a at hk ⊢
  generalize k x' = b at hk' ⊢
  rw [div_eq_div_iff hβ.ne' (by positivity), eq_div_iff hk.ne']
  constructor
  · intro h
    have : β * (x' * a) = β * (Φ x * b) := by linarith
    have := mul_left_cancel₀ hβ.ne' this
    linarith
  · intro h
    linear_combination (-β) * h

/-- Cochrane (2023), eq. (16.32), p. 393, and Woodford (2003), eq. (4.5), p. 125: with
`λ(i) = u_c[y, L(y, i)]` and Woodford's rule `φ(Π) = Φ(Π)/β − 1`, a positive path satisfies
(16.32) at every date iff it is a solution of Woodford's (4.5) (`GlobalDynamics.IsPath45`); so the
Schmitt-Grohé–Uribe results of `SGU` apply to (16.32). -/
theorem eq1632_iff_path45 {β : ℝ} {Φ lam : ℝ → ℝ} {infl : ℕ → ℝ} (hβ : 0 < β)
    (hlam : ∀ t, 0 < lam (Φ (infl t) / β - 1)) (hpos : ∀ t, 0 < infl t) :
    IsPath45 β lam (fun x => Φ x / β - 1) infl ↔
      ∀ t, infl (t + 1) =
        Φ (infl t) * lam (Φ (infl (t + 1)) / β - 1) / lam (Φ (infl t) / β - 1) := by
  unfold IsPath45
  simp only [hpos, implies_true, true_and]
  refine forall_congr' fun t => ?_
  have h1 := hlam t
  have h2 := hlam (t + 1)
  have hb : β * (1 + (Φ (infl t) / β - 1)) = Φ (infl t) := by field_simp; ring
  rw [hb]
  generalize lam (Φ (infl t) / β - 1) = a at h1 ⊢
  generalize lam (Φ (infl (t + 1)) / β - 1) = b at h2 ⊢
  rw [div_eq_div_iff h2.ne' h1.ne', eq_div_iff h1.ne']

/-- Cochrane (2023), (16.32), p. 393, correction: "the difference equation (16.32) may rise to
require `Π_{t+1} = ∞` above some bound `Π_U`, even if the policy rule for nominal interest rates
… remains bounded" cannot happen when the rule is continuous and bounded and `k = u_c ∘ L` is
continuous and positive on the (compact) range of interest rates the rule sets: then every
`Π_t > 0` has a finite successor `Π_{t+1} > 0` solving (16.32). An explosion in finite time needs
an unbounded rule (as in Schmitt-Grohé–Uribe, `SGU.sgu_no_successor`) or `u_c ∘ L` vanishing or
exploding at a finite rate (money demand hitting zero). -/
theorem successor_exists_of_bounded_rule {β ilo ihi : ℝ} {Φ k : ℝ → ℝ}
    (hk : ContinuousOn k (Set.Icc ilo ihi)) (hkpos : ∀ j ∈ Set.Icc ilo ihi, 0 < k j)
    (hΦc : ContinuousOn Φ (Set.Ioi 0)) (hΦpos : ∀ x, 0 < x → 0 < Φ x)
    (hΦr : ∀ x, 0 < x → Φ x / β - 1 ∈ Set.Icc ilo ihi) {x : ℝ} (hx : 0 < x) :
    ∃ x', 0 < x' ∧ x' = Φ x * k (Φ x' / β - 1) / k (Φ x / β - 1) := by
  have hne : (Set.Icc ilo ihi).Nonempty := ⟨_, hΦr x hx⟩
  obtain ⟨jm, hjm, hmin⟩ := isCompact_Icc.exists_isMinOn hne hk
  obtain ⟨jM, hjM, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hk
  set m := k jm with hm
  set M := k jM with hM
  have hm0 : 0 < m := hkpos jm hjm
  set H : ℝ → ℝ := fun z => k (Φ z / β - 1) with hH
  have hHb : ∀ z, 0 < z → m ≤ H z ∧ H z ≤ M := fun z hz =>
    ⟨hmin (hΦr z hz), hmax (hΦr z hz)⟩
  have hHc : ContinuousOn H (Set.Ioi 0) := by
    refine hk.comp (((hΦc.div_const β).sub continuousOn_const)) fun z hz => hΦr z hz
  set c := Φ x / H x with hc
  have hc0 : 0 < c := div_pos (hΦpos x hx) (lt_of_lt_of_le hm0 (hHb x hx).1)
  set a := c * m / 2 with ha
  set b := 2 * c * M with hb
  have ha0 : 0 < a := by positivity
  have hmM : m ≤ M := (hHb x hx).1.trans (hHb x hx).2
  have hab : a ≤ b := by
    rw [ha, hb]; nlinarith
  set G : ℝ → ℝ := fun z => z / H z with hG
  have hGc : ContinuousOn G (Set.Icc a b) := by
    have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha0 hz.1
    exact (continuousOn_id.mono hsub).div (hHc.mono hsub) fun z hz =>
      (lt_of_lt_of_le hm0 (hHb z (lt_of_lt_of_le ha0 hz.1)).1).ne'
  have hGa : G a ≤ c := by
    have h1 := (hHb a ha0).1
    simp only [hG]
    rw [div_le_iff₀ (lt_of_lt_of_le hm0 h1)]
    nlinarith
  have hGb : c ≤ G b := by
    have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
    have h1 := (hHb b hb0).2
    have h0 := lt_of_lt_of_le hm0 (hHb b hb0).1
    simp only [hG]
    rw [le_div_iff₀ h0]
    nlinarith
  obtain ⟨z, hz, hGz⟩ := intermediate_value_Icc hab hGc ⟨hGa, hGb⟩
  have hz0 : 0 < z := lt_of_lt_of_le ha0 hz.1
  have hHz : 0 < H z := lt_of_lt_of_le hm0 (hHb z hz0).1
  refine ⟨z, hz0, ?_⟩
  simp only [hG] at hGz
  have : z = c * H z := by rw [← hGz]; field_simp
  conv_lhs => rw [this]
  simp only [hc, hH]
  ring

/-- Cochrane (2023), (16.32), p. 393, correction (continued): under the hypotheses of
`successor_exists_of_bounded_rule`, every `Π₀ > 0` starts a perfect-foresight path of (16.32)
defined at all dates: no explosion in finite time. -/
theorem path_exists_of_bounded_rule {β ilo ihi : ℝ} {Φ k : ℝ → ℝ}
    (hk : ContinuousOn k (Set.Icc ilo ihi)) (hkpos : ∀ j ∈ Set.Icc ilo ihi, 0 < k j)
    (hΦc : ContinuousOn Φ (Set.Ioi 0)) (hΦpos : ∀ x, 0 < x → 0 < Φ x)
    (hΦr : ∀ x, 0 < x → Φ x / β - 1 ∈ Set.Icc ilo ihi) {x0 : ℝ} (hx0 : 0 < x0) :
    ∃ infl : ℕ → ℝ, infl 0 = x0 ∧ (∀ t, 0 < infl t) ∧
      ∀ t, infl (t + 1) = Φ (infl t) * k (Φ (infl (t + 1)) / β - 1) / k (Φ (infl t) / β - 1) := by
  classical
  have hs := fun x (hx : 0 < x) =>
    successor_exists_of_bounded_rule hk hkpos hΦc hΦpos hΦr hx
  let next : ℝ → ℝ := fun x => if hx : 0 < x then Classical.choose (hs x hx) else 1
  have hnext : ∀ x, 0 < x → 0 < next x ∧
      next x = Φ x * k (Φ (next x) / β - 1) / k (Φ x / β - 1) := fun x hx => by
    simp only [next, hx, ↓reduceDIte]
    exact Classical.choose_spec (hs x hx)
  have hpos : ∀ t, 0 < next^[t] x0 := by
    intro t
    induction t with
    | zero => simpa using hx0
    | succ n ih => rw [Function.iterate_succ_apply']; exact (hnext _ ih).1
  refine ⟨fun t => next^[t] x0, rfl, hpos, fun t => ?_⟩
  simp only [Function.iterate_succ_apply']
  exact (hnext _ (hpos t)).2

/-- Cochrane (2023), (16.32), p. 393, explicit bounded-rule model (`β = 1/2`): the Taylor rule
`Φ(Π) = max(1/2, min(2Π − 1, 3))` (target `Π* = 1`, slope 2 there), truncated below at the zero
bound and capped above, so `1/2 ≤ Φ ≤ 3`. -/
noncomputable def boundedRule (x : ℝ) : ℝ := max (1 / 2) (min (2 * x - 1) 3)

/-- Cochrane (2023), (16.32), p. 393: the nominal rate set by `boundedRule` with `β = 1/2`,
`i = Φ(Π)/β − 1 = 2Φ(Π) − 1 ∈ [0, 5]`. -/
noncomputable def boundedRate (x : ℝ) : ℝ := 2 * boundedRule x - 1

/-- Cochrane (2023), (16.32), p. 393: money demand `M/P = L(i) = 5 − i`, positive for `i < 5`
and vanishing at the finite rate `i = 5` (the rate the capped rule reaches at `Π ≥ 2`). -/
def moneyDemand (i : ℝ) : ℝ := 5 - i

/-- Cochrane (2023), (16.31), p. 393: marginal utility of consumption as a function of real
money, `u_c(y, m) = 1/m` (e.g. a cash constraint `c ≤ m` with log utility), so `u_c ∘ L` blows
up as `i ↑ 5`. -/
noncomputable def ucMoney (m : ℝ) : ℝ := 1 / m

/-- Cochrane (2023), (16.32), p. 393: the rate set by the bounded rule is
`max(0, min(4Π − 3, 5))`, so it is at least `min(4Π − 3, 5)`. -/
theorem boundedRate_ge (x : ℝ) : min (4 * x - 3) 5 ≤ boundedRate x := by
  unfold boundedRate boundedRule
  rcases le_total (2 * x - 1) 3 with h1 | h1
  · rw [min_eq_left h1]
    have := le_max_right (1 / 2 : ℝ) (2 * x - 1)
    have := min_le_left (4 * x - 3) 5
    linarith
  · rw [min_eq_right h1]
    have := le_max_right (1 / 2 : ℝ) 3
    have := min_le_right (4 * x - 3) 5
    linarith

/-- Cochrane (2023), (16.32), p. 393, "the difference equation (16.32) may rise to require
`Π_{t+1} = ∞` above some bound `Π_U`, even if the policy rule for nominal interest rates … remains
bounded", made exact. With `β = 1/2`, the bounded rule `boundedRule` (`1/2 ≤ Φ ≤ 3`, rates in
`[0, 5]`, target `Π* = 1` with `Φ′(Π*) = 2`), money demand `L(i) = 5 − i` and `u_c = 1/m`, the
composite `u_c ∘ L` blows up at the finite rate `i = 5`, and for every `Π_t ∈ (1, 3/2)` there is
no `Π_{t+1} > 0` with positive money demand solving (16.32): inflation slightly above target
requires infinite inflation next period. Together with `successor_exists_of_bounded_rule`
(necessity of a singular `u_c ∘ L` on the range of rates) this settles the book's claim. -/
theorem bounded_rule_explosion :
    (∀ x, 1 / 2 ≤ boundedRule x ∧ boundedRule x ≤ 3) ∧
      (∀ x, 0 ≤ boundedRate x ∧ boundedRate x ≤ 5) ∧
      boundedRule 1 = 1 ∧ HasDerivAt boundedRule 2 1 ∧
      (∀ i, i < 5 → 0 < moneyDemand i) ∧
      Tendsto (fun i => ucMoney (moneyDemand i)) (𝓝[<] 5) atTop ∧
      ∀ x ∈ Set.Ioo (1 : ℝ) (3 / 2), ¬ ∃ x', 0 < x' ∧ 0 < moneyDemand (boundedRate x') ∧
        x' = boundedRule x * ucMoney (moneyDemand (boundedRate x')) /
          ucMoney (moneyDemand (boundedRate x)) := by
  have hbd : ∀ x, 1 / 2 ≤ boundedRule x ∧ boundedRule x ≤ 3 := fun x =>
    ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  refine ⟨hbd, fun x => ?_, ?_, ?_, fun i hi => by unfold moneyDemand; linarith, ?_, ?_⟩
  · unfold boundedRate; constructor <;> linarith [hbd x]
  · norm_num [boundedRule]
  · have h : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).const_mul 2).sub_const 1
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)]
      with y hy
    unfold boundedRule
    rw [min_eq_left (by linarith [hy.2]), max_eq_right (by linarith [hy.1])]
  · have h1 : Tendsto (fun i : ℝ => moneyDemand i) (𝓝[<] 5) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun i : ℝ => 5 - i) (𝓝 5) (𝓝 (5 - 5)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with i hi
        simp only [Set.mem_Ioi, moneyDemand]
        linarith [Set.mem_Iio.mp hi]
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    refine h2.congr fun i => ?_
    simp [ucMoney]
  · rintro x hx ⟨x', hx'0, hL, heq⟩
    have hΦ : boundedRule x = 2 * x - 1 := by
      unfold boundedRule
      rw [min_eq_left (by linarith [hx.2]), max_eq_right (by linarith [hx.1])]
    have hr : boundedRate x = 4 * x - 3 := by unfold boundedRate; rw [hΦ]; ring
    have hLx : 0 < moneyDemand (boundedRate x) := by
      rw [hr]; unfold moneyDemand; linarith [hx.2]
    -- `x' · L(i(x')) = Φ(x) · L(i(x)) = (2x − 1)(8 − 4x) > 4`
    have hprod : x' * moneyDemand (boundedRate x') =
        (2 * x - 1) * moneyDemand (boundedRate x) := by
      rw [← hΦ]
      generalize moneyDemand (boundedRate x') = A at heq hL ⊢
      generalize moneyDemand (boundedRate x) = B at heq hLx ⊢
      rw [heq]
      unfold ucMoney
      field_simp
    have hbig : 4 < (2 * x - 1) * moneyDemand (boundedRate x) := by
      rw [hr]; unfold moneyDemand; nlinarith [hx.1, hx.2]
    -- but `x' · L(i(x')) ≤ 4` whenever money demand is positive
    have hge := boundedRate_ge x'
    have hsmall : x' * moneyDemand (boundedRate x') ≤ 4 := by
      rcases le_total (4 * x' - 3) 5 with h1 | h1
      · rw [min_eq_left h1] at hge
        unfold moneyDemand
        nlinarith [sq_nonneg (x' - 1)]
      · rw [min_eq_right h1] at hge
        unfold moneyDemand at hL
        linarith
    linarith

/-! ## §16.10.4 Threaten negative nominal rates (Bassetto) -/

/-- Cochrane (2023), §16.10.4, p. 391, Bassetto (2004): if the rule ignores the zero bound and
`Π*` is its only steady state on `[β, Π*]` — `Φ` continuous there with `Φ(Π) < Π` on `[β, Π*)` —
then every path of (16.29) starting in `[β, Π*)` reaches `Π_{t+1} < β`, i.e. `i_t < 0`, in finite
time ("the minute we pass the zero bound, no equilibrium can form"). -/
theorem bassetto_exit {Φ : ℝ → ℝ} {β Pis : ℝ} {infl : ℕ → ℝ}
    (hcont : ContinuousOn Φ (Set.Icc β Pis)) (hbelow : ∀ x ∈ Set.Ico β Pis, Φ x < x)
    (hpath : ∀ t, infl (t + 1) = Φ (infl t)) (h0 : infl 0 ∈ Set.Ico β Pis) :
    ∃ t, infl (t + 1) < β := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ t, infl t ∈ Set.Ico β Pis := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      refine ⟨hcon n, ?_⟩
      rw [hpath]; exact lt_trans (hbelow _ ih) ih.2
  have hanti : Antitone infl := antitone_nat_of_succ_le fun t => by
    rw [hpath]; exact (hbelow _ (hmem t)).le
  have hbdd : BddBelow (Set.range infl) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hmem t).1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ t, infl t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hmem t).1
  have hL0 : L ≤ infl 0 := ciInf_le hbdd 0
  have hLmem : L ∈ Set.Icc β Pis := ⟨hLβ, hL0.trans h0.2.le⟩
  have hwithin : Tendsto infl atTop (𝓝[Set.Icc β Pis] L) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun t => ⟨(hmem t).1, (hmem t).2.le⟩⟩
  have h1 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 (Φ L)) :=
    (hcont L hLmem).tendsto.comp hwithin
  have h2 : Tendsto (fun t => Φ (infl t)) atTop (𝓝 L) := by
    have : (fun t => Φ (infl t)) = fun t => infl (t + 1) := funext fun t => (hpath t).symm
    rw [this]; exact (tendsto_add_atTop_iff_nat 1).mpr hlim
  have hfix := tendsto_nhds_unique h1 h2
  have := hbelow L ⟨hLβ, lt_of_le_of_lt hL0 h0.2⟩
  linarith

/-- Cochrane (2023), §16.10.4, pp. 391–392, "such a `Φ(Π)` function cleanly rules out
deflationary equilibria": under Bassetto's rule there is no equilibrium (with the zero bound,
`LowerBound.IsEquilibrium`) whose initial inflation lies in `[β, Π*)`. -/
theorem bassetto_no_equilibrium {r : ℝ} {Φ : ℝ → ℝ} {Pis Pm1 : ℝ} {P i s D : ℕ → ℝ}
    (hr : 0 < 1 + r) (hcont : ContinuousOn Φ (Set.Icc (1 + r)⁻¹ Pis))
    (hbelow : ∀ x ∈ Set.Ico (1 + r)⁻¹ Pis, Φ x < x) (h : IsEquilibrium r Φ Pm1 P i s D)
    (h0 : infl Pm1 P 0 ∈ Set.Ico (1 + r)⁻¹ Pis) : False := by
  obtain ⟨hdyn, hzb, -, -⟩ := equilibrium_dynamics hr h
  obtain ⟨t, ht⟩ := bassetto_exit hcont hbelow hdyn h0
  linarith [hzb t]

/-- Cochrane (2023), §16.10.4, p. 391: the linear rule `Φ(Π) = Π* + φ(Π − Π*)`, `φ > 1`, applied
without the zero bound. -/
def linRule (Pis φ : ℝ) (x : ℝ) : ℝ := Pis + φ * (x - Pis)

/-- Cochrane (2023), §16.10.4, pp. 391–392: the linear rule satisfies Bassetto's hypotheses
(continuous, `Φ(Π) < Π` below `Π*`), the gap below target grows as `φᵗ`, and above `Π*` the
inflationary paths stay above `Π*` — those equilibria are not removed. -/
theorem linear_rule_exit {Pis φ : ℝ} (hφ : 1 < φ) :
    Continuous (linRule Pis φ) ∧ (∀ x, x < Pis → linRule Pis φ x < x) ∧
      (∀ x0 t, Pis - (linRule Pis φ)^[t] x0 = φ ^ t * (Pis - x0)) ∧
      ∀ x0 t, Pis ≤ x0 → Pis ≤ (linRule Pis φ)^[t] x0 := by
  have hgap : ∀ x0 t, Pis - (linRule Pis φ)^[t] x0 = φ ^ t * (Pis - x0) := by
    intro x0 t
    induction t with
    | zero => simp
    | succ n ih =>
      rw [orbit_succ]
      simp only [linRule]
      rw [pow_succ]
      linear_combination φ * ih
  refine ⟨by unfold linRule; fun_prop, fun x hx => ?_, hgap, fun x0 t hx0 => ?_⟩
  · simp only [linRule]; nlinarith
  · have := hgap x0 t
    have : φ ^ t * (Pis - x0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (by linarith) t) (by linarith)
    linarith

/-! ## §16.10.5 Weird Taylor rules -/

/-- Cochrane (2023), §16.10.5, p. 392, Woodford (2003, p. 136): if the rule becomes vertical at
`Π_U > Π*` (`Φ(Π) → ∞` as `Π ↑ Π_U`), is continuous on `(Π*, Π_U)` with `Φ(Π) > Π` there, then
every path starting in `(Π*, Π_U)` reaches `Π_U` in finite time — infinite inflation, an
explosion "in finite time". -/
theorem vertical_rule_exit {Φ : ℝ → ℝ} {Pis PiU : ℝ} {infl : ℕ → ℝ}
    (hcont : ContinuousOn Φ (Set.Ioo Pis PiU)) (habove : ∀ x ∈ Set.Ioo Pis PiU, x < Φ x)
    (hvert : Tendsto Φ (𝓝[<] PiU) atTop) (hpath : ∀ t, infl (t + 1) = Φ (infl t))
    (h0 : infl 0 ∈ Set.Ioo Pis PiU) : ∃ t, PiU ≤ infl t := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ t, infl t ∈ Set.Ioo Pis PiU := by
    intro t
    induction t with
    | zero => exact h0
    | succ n ih =>
      refine ⟨?_, hcon (n + 1)⟩
      rw [hpath]; exact lt_trans ih.1 (habove _ ih)
  have hmono : Monotone infl := monotone_nat_of_le_succ fun t => by
    rw [hpath]; exact (habove _ (hmem t)).le
  have hbdd : BddAbove (Set.range infl) := ⟨PiU, by rintro _ ⟨t, rfl⟩; exact (hmem t).2.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ t, infl t with hL
  have hLU : L ≤ PiU := ciSup_le fun t => (hmem t).2.le
  have hL0 : infl 0 ≤ L := le_ciSup hbdd 0
  rcases hLU.lt_or_eq with hlt | heq
  · have hLmem : L ∈ Set.Ioo Pis PiU := ⟨lt_of_lt_of_le h0.1 hL0, hlt⟩
    have hfix := fixed_of_tendsto hpath hlim (hcont.continuousAt (Ioo_mem_nhds hLmem.1 hLmem.2))
    linarith [habove L hLmem]
  · have hw : Tendsto infl atTop (𝓝[<] PiU) :=
      tendsto_nhdsWithin_iff.mpr ⟨heq ▸ hlim, Eventually.of_forall fun t => (hmem t).2⟩
    have h1 : Tendsto (fun t => infl (t + 1)) atTop atTop := by
      have : (fun t => infl (t + 1)) = fun t => Φ (infl t) := funext hpath
      rw [this]; exact hvert.comp hw
    obtain ⟨t, ht⟩ := (h1.eventually (eventually_gt_atTop PiU)).exists
    linarith [(hmem (t + 1)).2]

/-- Cochrane (2023), §16.10.5, p. 392, Alstadheim and Henderson (2006): if the rule sends every
`Π ≠ Π*` above `Π*`, lies above the diagonal above `Π*` and is continuous there, every positive
path not starting at `Π*` explodes. -/
theorem v_rule_unbounded {Φ : ℝ → ℝ} {Pis : ℝ} {infl : ℕ → ℝ}
    (hjump : ∀ x, 0 < x → x ≠ Pis → Pis < Φ x) (habove : ∀ x, Pis < x → x < Φ x)
    (hcont : ContinuousOn Φ (Set.Ioi Pis)) (hpath : ∀ t, infl (t + 1) = Φ (infl t))
    (hpos : 0 < infl 0) (hne : infl 0 ≠ Pis) : Tendsto infl atTop atTop := by
  have h1 : Pis < infl 1 := by rw [hpath]; exact hjump _ hpos hne
  have hup : ∀ n, Pis < infl (n + 1) ∧ infl (n + 1) < infl (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h1, by rw [hpath 1]; exact habove _ h1⟩
    | succ n ih =>
      have h2 : Pis < infl (n + 2) := lt_trans ih.1 ih.2
      exact ⟨h2, by rw [hpath (n + 2)]; exact habove _ h2⟩
  set y : ℕ → ℝ := fun n => infl (n + 1) with hy
  have hypath : ∀ n, y (n + 1) = Φ (y n) := fun n => hpath (n + 1)
  have hymono : Monotone y := monotone_nat_of_le_succ fun n => (hup n).2.le
  rcases monotone_orbit_atTop_or_fixed hypath hymono with htop | ⟨L, -, hLb, hfix⟩
  · exact (tendsto_add_atTop_iff_nat 1).mp htop
  · exfalso
    have hL : Pis < L := lt_of_lt_of_le (hup 0).1 (hLb 0)
    have := hfix (hcont.continuousAt (Ioi_mem_nhds hL))
    linarith [habove L hL]

/-- Cochrane (2023), §16.10.5, p. 392: under the hypotheses of `v_rule_unbounded` with
`Φ(Π*) = Π*`, the target is the unique bounded positive equilibrium path. -/
theorem v_rule_unique_bounded {Φ : ℝ → ℝ} {Pis : ℝ} {infl : ℕ → ℝ}
    (hjump : ∀ x, 0 < x → x ≠ Pis → Pis < Φ x) (habove : ∀ x, Pis < x → x < Φ x)
    (hcont : ContinuousOn Φ (Set.Ioi Pis)) (hpath : ∀ t, infl (t + 1) = Φ (infl t))
    (hpos : ∀ t, 0 < infl t) (hbdd : BddAbove (Set.range infl)) : ∀ t, infl t = Pis := by
  intro t
  by_contra hne
  have := v_rule_unbounded (infl := fun s => infl (t + s)) hjump habove hcont
    (fun s => by rw [← add_assoc]; exact hpath _) (hpos t) (by simpa using hne)
  obtain ⟨M, hM⟩ := hbdd
  obtain ⟨s, hs⟩ := (this.eventually (eventually_gt_atTop M)).exists
  linarith [hM ⟨t + s, rfl⟩]

/-- Cochrane (2023), §16.10.5, p. 392: a V-shaped rule touching the 45° line only at `Π*`,
`Φ(Π) = Π* + 2|Π − Π*|`. -/
noncomputable def vRule (Pis : ℝ) (x : ℝ) : ℝ := Pis + 2 * |x - Pis|

/-- Cochrane (2023), §16.10.5, p. 392: the V-shaped rule satisfies the hypotheses of
`v_rule_unique_bounded` and never sets inflation below `Π*` (so it respects the zero bound when
`Π* ≥ β`). -/
theorem vRule_props (Pis : ℝ) :
    vRule Pis Pis = Pis ∧ (∀ x, x ≠ Pis → Pis < vRule Pis x) ∧
      (∀ x, Pis < x → x < vRule Pis x) ∧ Continuous (vRule Pis) ∧
      ∀ x, Pis ≤ vRule Pis x := by
  refine ⟨by simp [vRule], fun x hx => ?_, fun x hx => ?_, by unfold vRule; fun_prop,
    fun x => ?_⟩
  · have : 0 < |x - Pis| := abs_pos.mpr (sub_ne_zero.mpr hx)
    simp only [vRule]; linarith
  · simp only [vRule]; rw [abs_of_pos (by linarith)]; linarith
  · simp only [vRule]; linarith [abs_nonneg (x - Pis)]

/-- Cochrane (2023), §16.10.5, p. 392, Alstadheim and Henderson (2006): a discontinuous rule that
jumps from below `Π*` to above it, `Φ(Π) = Π* + 1` for `Π < Π*`, `Φ(Π) = Π* + 2(Π − Π*)` for
`Π ≥ Π*`. -/
noncomputable def ahJump (Pis : ℝ) (x : ℝ) : ℝ := if x < Pis then Pis + 1 else Pis + 2 * (x - Pis)

/-- Cochrane (2023), §16.10.5, p. 392: the discontinuous rule `ahJump` satisfies the hypotheses
of `v_rule_unique_bounded`. -/
theorem ahJump_props (Pis : ℝ) :
    ahJump Pis Pis = Pis ∧ (∀ x, x ≠ Pis → Pis < ahJump Pis x) ∧
      (∀ x, Pis < x → x < ahJump Pis x) ∧ ContinuousOn (ahJump Pis) (Set.Ioi Pis) := by
  refine ⟨by simp [ahJump], fun x hx => ?_, fun x hx => ?_, ?_⟩
  · unfold ahJump
    split_ifs with h
    · linarith
    · push Not at h; have := lt_of_le_of_ne h (Ne.symm hx); linarith
  · have hn : ¬ x < Pis := not_lt.mpr hx.le
    simp only [ahJump, hn, ↓reduceIte]
    linarith
  · have : Set.EqOn (ahJump Pis) (fun x => Pis + 2 * (x - Pis)) (Set.Ioi Pis) := fun x hx => by
      have hn : ¬ x < Pis := not_lt.mpr (le_of_lt (Set.mem_Ioi.mp hx))
      simp only [ahJump, hn, ↓reduceIte]
    exact (ContinuousOn.congr (by fun_prop) this)

/-- Cochrane (2023), §16.10.5, p. 392: a rule tangent to the 45° line at `Π*`,
`Φ(Π) = Π + (Π − Π*)²`, which touches the line only at `Π*`. -/
def tangentRule (Pis : ℝ) (x : ℝ) : ℝ := x + (x - Pis) ^ 2

/-- Cochrane (2023), §16.10.5, p. 392: touching the 45° line only at `Π*` is not enough. The
tangent rule has `Π*` as its only steady state and respects the bound `Φ ≥ Π* − 1/4`, but every
path starting in `(Π* − 1, Π*)` is a bounded, nonconstant path converging to `Π*`: a continuum
of bounded equilibria. The V-shaped rules work because they jump *over* `Π*`. -/
theorem tangent_rule_converges {Pis : ℝ} {infl : ℕ → ℝ}
    (hpath : ∀ t, infl (t + 1) = tangentRule Pis (infl t)) (h0 : infl 0 ∈ Set.Ioo (Pis - 1) Pis) :
    (∀ x, tangentRule Pis x = x ↔ x = Pis) ∧ (∀ x, Pis - 1 / 4 ≤ tangentRule Pis x) ∧
      (∀ t, infl 0 ≤ infl t ∧ infl t < Pis) ∧ Tendsto infl atTop (𝓝 Pis) := by
  have hstep : ∀ x ∈ Set.Ioo (Pis - 1) Pis, x < tangentRule Pis x ∧ tangentRule Pis x < Pis :=
    fun x hx => by
      simp only [tangentRule]
      constructor
      · nlinarith [hx.2]
      · nlinarith [hx.1, hx.2]
  have hmem : ∀ t, infl t ∈ Set.Ioo (Pis - 1) Pis ∧ infl 0 ≤ infl t := by
    intro t
    induction t with
    | zero => exact ⟨h0, le_rfl⟩
    | succ n ih =>
      rw [hpath]
      have := hstep _ ih.1
      exact ⟨⟨by linarith [ih.1.1], this.2⟩, by linarith [ih.2]⟩
  refine ⟨fun x => ⟨fun h => ?_, fun h => by simp [tangentRule, h]⟩, fun x => ?_,
    fun t => ⟨(hmem t).2, (hmem t).1.2⟩, ?_⟩
  · simp only [tangentRule, add_eq_left] at h
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h
    linarith
  · simp only [tangentRule]; nlinarith [sq_nonneg (x - Pis + 1 / 2)]
  · have hmono : Monotone infl := monotone_nat_of_le_succ fun t => by
      rw [hpath]; exact (hstep _ (hmem t).1).1.le
    rcases monotone_orbit_atTop_or_fixed hpath hmono with htop | ⟨L, hL, hLb, hfix⟩
    · exfalso
      obtain ⟨t, ht⟩ := (htop.eventually (eventually_gt_atTop Pis)).exists
      linarith [(hmem t).1.2]
    · have hLP : L ≤ Pis := le_of_tendsto' hL fun t => (hmem t).1.2.le
      have hc : ContinuousAt (tangentRule Pis) L := by unfold tangentRule; fun_prop
      have hfx := hfix hc
      simp only [tangentRule, add_eq_left] at hfx
      have : L = Pis := by
        have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hfx
        linarith
      rw [this] at hL
      exact hL

/-! ## §16.10.6 Residual money demand: Sims (1994) -/

/-- Cochrane (2023), §16.10.6, pp. 393–394, Sims (1994): "perhaps there is a lower limit on
nominal money demand … then real money demand explodes in a deflation violating the
transversality condition". Precisely: if nominal money stays above `M̲ > 0`, prices follow
`P_{t+1} = Π_{t+1}P_t` with `Π_{t+1} ≥ β` (the zero bound), and the deflation approaches `β` fast
enough that `Σ (Π_{t+1} − β) < ∞`, then the discounted real money `βᵀM_T/P_T` does not tend to
zero: the transversality condition fails. -/
theorem sims_tvc_violated {β Mlow : ℝ} {infl P M : ℕ → ℝ} (hβ : 0 < β) (hP0 : 0 < P 0)
    (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t) (hge : ∀ t, β ≤ infl (t + 1))
    (hsum : Summable fun t => infl (t + 1) - β) (hMlow : 0 < Mlow) (hM : ∀ t, Mlow ≤ M t) :
    ¬ Tendsto (fun T => β ^ T * M T / P T) atTop (𝓝 0) := by
  set a : ℕ → ℝ := fun k => (infl (k + 1) - β) / β with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => div_nonneg (by linarith [hge k]) hβ.le
  have hasum : Summable a := hsum.div_const β
  set S := ∑' k, a k with hS
  have hinfl : ∀ t, 0 < infl (t + 1) := fun t => lt_of_lt_of_le hβ (hge t)
  have hP : ∀ t, 0 < P t := by
    intro t
    induction t with
    | zero => exact hP0
    | succ n ih => rw [hPrec]; exact mul_pos (hinfl n) ih
  set q : ℕ → ℝ := fun T => β ^ T / P T with hq
  have hqstep : ∀ T, q (T + 1) = q T * (β / infl (T + 1)) := fun T => by
    simp only [hq, hPrec, pow_succ]
    have := hP T
    have := hinfl T
    field_simp
  -- `β/Π ≥ exp(−(Π/β − 1))`
  have hratio : ∀ T, Real.exp (-a T) ≤ β / infl (T + 1) := fun T => by
    have h1 : infl (T + 1) / β ≤ Real.exp (a T) := by
      have := Real.add_one_le_exp (a T)
      simp only [ha] at this ⊢
      have e : (infl (T + 1) - β) / β + 1 = infl (T + 1) / β := by field_simp; ring
      linarith
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (hinfl T)]
    rw [div_le_iff₀ hβ] at h1
    linarith
  have hqlow : ∀ T, q 0 * Real.exp (-∑ k ∈ Finset.range T, a k) ≤ q T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [hqstep, Finset.sum_range_succ, neg_add, Real.exp_add, ← mul_assoc]
      have hq0 : 0 ≤ q n := le_trans (by
        have : 0 < q 0 := by simp only [hq]; exact div_pos (pow_pos hβ 0) hP0
        positivity) ih
      exact mul_le_mul ih (hratio n) (Real.exp_pos _).le hq0
  have hq0 : 0 < q 0 := by simp only [hq]; exact div_pos (pow_pos hβ 0) hP0
  have hbound : ∀ T, q 0 * Real.exp (-S) ≤ q T := fun T => by
    refine le_trans ?_ (hqlow T)
    apply mul_le_mul_of_nonneg_left _ hq0.le
    apply Real.exp_le_exp.mpr
    have := hasum.sum_le_tsum (Finset.range T) (fun k _ => ha0 k)
    linarith
  have hc : 0 < Mlow * (q 0 * Real.exp (-S)) := by positivity
  intro hlim
  have hev : ∀ᶠ T in atTop, Mlow * (q 0 * Real.exp (-S)) ≤ β ^ T * M T / P T :=
    Eventually.of_forall fun T => by
      have h1 := hbound T
      have h2 : β ^ T * M T / P T = M T * q T := by simp only [hq]; ring
      rw [h2]
      exact mul_le_mul (hM T) h1 (by positivity) (by linarith [hM T])
  have := ge_of_tendsto hlim hev
  linarith

/-- Cochrane (2023), §16.10.6, p. 394: in particular, when the deflation reaches the zero bound
in finite time (`Π_t = β` from some date on, as with the truncated rule
`LowerBound.truncRule_hits_bound`), Sims's argument applies. -/
theorem sims_tvc_violated_of_eventually_beta {β Mlow : ℝ} {infl P M : ℕ → ℝ} (hβ : 0 < β)
    (hP0 : 0 < P 0) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t) (hge : ∀ t, β ≤ infl (t + 1))
    {T0 : ℕ} (hT0 : ∀ t, T0 ≤ t → infl (t + 1) = β) (hMlow : 0 < Mlow) (hM : ∀ t, Mlow ≤ M t) :
    ¬ Tendsto (fun T => β ^ T * M T / P T) atTop (𝓝 0) := by
  refine sims_tvc_violated hβ hP0 hPrec hge ?_ hMlow hM
  refine summable_of_ne_finset_zero (s := Finset.range T0) fun t ht => ?_
  rw [Finset.mem_range, not_lt] at ht
  rw [hT0 t ht, sub_self]

/-- Cochrane (2023), §16.10.6, p. 394, imprecision: the penny in the sock drawer does not bite
when the deflation converges to a steady state `Π_L > β` (the zero bound not reached): with
constant money `M̲`, the discounted real money `βᵀM̲/P_T` tends to zero, so the transversality
condition holds. -/
theorem sims_no_bite_above_beta {β Mlow PL : ℝ} {infl P : ℕ → ℝ} (hβ : 0 < β) (hPL : β < PL)
    (hP0 : 0 < P 0) (hPrec : ∀ t, P (t + 1) = infl (t + 1) * P t) (hpos : ∀ t, 0 < infl t)
    (hlim : Tendsto infl atTop (𝓝 PL)) :
    Tendsto (fun T => β ^ T * Mlow / P T) atTop (𝓝 0) := by
  have hP : ∀ t, 0 < P t := by
    intro t
    induction t with
    | zero => exact hP0
    | succ n ih => rw [hPrec]; exact mul_pos (hpos _) ih
  set c := (β + PL) / 2 with hc
  have hβc : β < c := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds (by linarith : c < PL)))
  set q : ℕ → ℝ := fun T => β ^ T / P T with hq
  have hqpos : ∀ T, 0 < q T := fun T => div_pos (pow_pos hβ T) (hP T)
  have hqstep : ∀ T, q (T + 1) = q T * (β / infl (T + 1)) := fun T => by
    simp only [hq, hPrec, pow_succ]
    have := hP T
    have := hpos (T + 1)
    field_simp
  have hdecay : ∀ n, q (T0 + n) ≤ q T0 * (β / c) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, hqstep, pow_succ, ← mul_assoc]
      have h1 : β / infl (T0 + n + 1) ≤ β / c :=
        div_le_div_of_nonneg_left hβ.le hc0 (hT0 _ (by omega)).le
      exact mul_le_mul ih h1 (div_pos hβ (hpos _)).le (by have := hqpos T0; positivity)
  have hr0 : 0 ≤ β / c := (div_pos hβ hc0).le
  have hr1 : β / c < 1 := (div_lt_one hc0).mpr hβc
  have hlim0 : Tendsto (fun T => q T0 * (β / c) ^ (T - T0)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (tendsto_sub_atTop_nat T0)).const_mul (q T0)
    simpa using this
  have hq0 : Tendsto q atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun T => (hqpos T).le) ?_ hlim0
    filter_upwards [eventually_ge_atTop T0] with T hT
    have := hdecay (T - T0)
    rwa [Nat.add_sub_cancel' hT] at this
  have : (fun T => β ^ T * Mlow / P T) = fun T => Mlow * q T := by
    funext T; simp only [hq]; ring
  rw [this]
  simpa using hq0.const_mul Mlow

/-- Cochrane (2023), §16.10.6, p. 394, imprecision: summability cannot be dropped from
`sims_tvc_violated`. With `Π_{t+1} = β(t + 2)/(t + 1) ≥ β`, converging to the zero-bound rate
`β`, and `P_T = βᵀ(T + 1)`, constant money `M̲` gives `βᵀM̲/P_T = M̲/(T + 1) → 0`: a deflation
converging slowly to the zero bound satisfies the transversality condition despite the
penny. -/
theorem sims_slow_counterexample {β Mlow : ℝ} (hβ : 0 < β) :
    let infl : ℕ → ℝ := fun t => β * ((t : ℝ) + 1) / t
    let P : ℕ → ℝ := fun T => β ^ T * ((T : ℝ) + 1)
    (∀ t, P (t + 1) = infl (t + 1) * P t) ∧ (∀ t, β ≤ infl (t + 1)) ∧
      Tendsto infl atTop (𝓝 β) ∧ Tendsto (fun T => β ^ T * Mlow / P T) atTop (𝓝 0) := by
  intro infl P
  refine ⟨fun t => ?_, fun t => ?_, ?_, ?_⟩
  · simp only [infl, P]
    push_cast
    have : (t : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · simp only [infl]
    push_cast
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have h1 : Tendsto (fun t : ℕ => β * (1 + 1 / (t : ℝ))) atTop (𝓝 (β * (1 + 0))) :=
      (tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat).const_mul β
    rw [add_zero, mul_one] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    simp only [infl]
    have : (t : ℝ) ≠ 0 := by positivity
    field_simp
  · have h1 : Tendsto (fun T : ℕ => Mlow * (1 / ((T : ℝ) + 1))) atTop (𝓝 (Mlow * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul Mlow
    rw [mul_zero] at h1
    refine h1.congr fun T => ?_
    simp only [P]
    have : β ^ T ≠ 0 := (pow_pos hβ T).ne'
    field_simp

/-! ## Online Appendix A3, §3.1.1–3.1.2: helicopter money versus open-market operations -/

/-- Cochrane (2023), Online Appendix A3, eq. (3.1) and p. 614: with no debt, budget
`(M_t − M_{t−1})/P_t = −s_t` and `P_{t+1} = βP_t` (`i = 0`), the present-value relation
"final money equals initial money plus added money" holds:
`M_{t−1}/P_t = Σ_{j<T} βʲ s_{t+j} + βᵀM_{t+T−1}/P_{t+T}`, and the last term equals
`M_{t+T−1}/P_t`. Here `M t` is money held into period `t` (the book's `M_{t−1}`). -/
theorem a3_helicopter_pv {β : ℝ} {M P s : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t)
    (hbud : ∀ t, (M (t + 1) - M t) / P t = -s t) (hdefl : ∀ t, P (t + 1) = β * P t) (t T : ℕ) :
    M t / P t = ∑ j ∈ Finset.range T, β ^ j * s (t + j) + β ^ T * (M (t + T) / P (t + T)) ∧
      β ^ T * (M (t + T) / P (t + T)) = M (t + T) / P t := by
  have hPT : ∀ n, P (t + n) = β ^ n * P t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [← add_assoc, hdefl, ih, pow_succ]; ring
  have hflow : ∀ u, M (u + 1) / P (u + 1) = (1 + (β⁻¹ - 1)) * (M u / P u - s u) := fun u => by
    have h := hbud u
    have := hP u
    rw [hdefl]
    field_simp at h ⊢
    linarith
  have hr : 0 < 1 + (β⁻¹ - 1) := by simp [hβ]
  have hpv := Hyperinflation.pv_partial (b := fun u => M u / P u) hr hflow t T
  simp only [add_sub_cancel, inv_inv] at hpv
  refine ⟨hpv, ?_⟩
  rw [hPT T]
  have := hP t
  have := pow_pos hβ T
  field_simp

/-- Cochrane (2023), Online Appendix A3, p. 614, "the final term grows at rate `(1+µ)ᵀ`. The
final, transversality condition is violated": with perpetual money growth `M_{t+1} = (1 + µ)M_t`,
`µ > 0`, `M_0 > 0`, and `P_{t+1} = βP_t`, the discounted real money `βᵀM_T/P_T` diverges. -/
theorem a3_helicopter_tvc_violated {β μ : ℝ} {M P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hP0 : 0 < P 0) (hM0 : 0 < M 0) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t)
    (hdefl : ∀ t, P (t + 1) = β * P t) :
    Tendsto (fun T => β ^ T * (M T / P T)) atTop atTop := by
  have hPT : ∀ n, P n = β ^ n * P 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hdefl, ih, pow_succ]; ring
  have hMT : ∀ n, M n = (1 + μ) ^ n * M 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hgrow, ih, pow_succ]; ring
  have : (fun T => β ^ T * (M T / P T)) = fun T => (1 + μ) ^ T * (M 0 / P 0) := by
    funext T
    rw [hPT, hMT]
    have := pow_pos hβ T
    field_simp
  rw [this]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).atTop_mul_const (div_pos hM0 hP0)

/-- Cochrane (2023), Online Appendix A3, §3.1.2, p. 615: with debt and open-market operations,
total liabilities `W_t = B_{t−1} + M_{t−1}` satisfy `W_t/P_t = W_{t+1}/P_t + s_t`; the surplus
`s_t = (1 − β)W_t/P_t` with `P_{t+1} = βP_t` gives constant real total debt
`W_{t+1}/P_{t+1} = W_t/P_t` and nominal total debt `W_{t+1} = βW_t`. -/
theorem a3_omo_real_const {β : ℝ} {W P s : ℕ → ℝ} (hβ : 0 < β) (hP : ∀ t, 0 < P t)
    (hbud : ∀ t, W t / P t = W (t + 1) / P t + s t) (hs : ∀ t, s t = (1 - β) * (W t / P t))
    (hdefl : ∀ t, P (t + 1) = β * P t) (t : ℕ) :
    W (t + 1) / P (t + 1) = W t / P t ∧ W (t + 1) = β * W t := by
  have h := hbud t
  rw [hs] at h
  have := hP t
  have hW : W (t + 1) = β * W t := by
    field_simp at h
    linarith
  refine ⟨?_, hW⟩
  rw [hW, hdefl]
  field_simp

/-- Cochrane (2023), Online Appendix A3, p. 616: under the OMO policy, `B_t + M_t = βᵗ(B_0 + M_0)`
and, with money growing at `1 + µ`, `B_t = βᵗ(B_0 + M_0) − (1 + µ)ᵗM_0`. -/
theorem a3_omo_nominal {β μ : ℝ} {B M W : ℕ → ℝ} (hW : ∀ t, W t = B t + M t)
    (hWstep : ∀ t, W (t + 1) = β * W t) (hgrow : ∀ t, M (t + 1) = (1 + μ) * M t) (t : ℕ) :
    W t = β ^ t * (B 0 + M 0) ∧ B t = β ^ t * (B 0 + M 0) - (1 + μ) ^ t * M 0 := by
  have hWt : ∀ n, W n = β ^ n * (B 0 + M 0) := by
    intro n
    induction n with
    | zero => simp [hW]
    | succ n ih => rw [hWstep, ih, pow_succ]; ring
  have hMt : ∀ n, M n = (1 + μ) ^ n * M 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hgrow, ih, pow_succ]; ring
  refine ⟨hWt t, ?_⟩
  have := hW t
  rw [hWt t, hMt t] at this
  linarith

/-- Cochrane (2023), Online Appendix A3, p. 616, "the second term grows without bound, so
government debt becomes negative": with `0 < β < 1`, `µ ≥ 0` and `M_0 > 0`, eventually
`B_t < 0`. -/
theorem a3_omo_debt_negative {β μ B0 M0 : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hμ : 0 ≤ μ)
    (hM0 : 0 < M0) :
    ∀ᶠ t in atTop, β ^ t * (B0 + M0) - (1 + μ) ^ t * M0 < 0 := by
  have h1 : Tendsto (fun t : ℕ => β ^ t * (B0 + M0)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const (B0 + M0)
  filter_upwards [h1.eventually (gt_mem_nhds hM0)] with t ht
  have : M0 ≤ (1 + μ) ^ t * M0 := le_mul_of_one_le_left hM0.le (one_le_pow₀ (by linarith))
  linarith

/-- Cochrane (2023), Online Appendix A3, p. 615, "despite ever increasing money, the total value
of government debt is the same, and the transversality condition holds": under the OMO policy
the discounted real total debt `βᵀW_T/P_T = βᵀW_0/P_0` tends to zero. -/
theorem a3_omo_tvc {β : ℝ} {W P s : ℕ → ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hP : ∀ t, 0 < P t)
    (hbud : ∀ t, W t / P t = W (t + 1) / P t + s t) (hs : ∀ t, s t = (1 - β) * (W t / P t))
    (hdefl : ∀ t, P (t + 1) = β * P t) :
    Tendsto (fun T => β ^ T * (W T / P T)) atTop (𝓝 0) := by
  have hconst : ∀ T, W T / P T = W 0 / P 0 := by
    intro T
    induction T with
    | zero => rfl
    | succ n ih => rw [(a3_omo_real_const hβ hP hbud hs hdefl n).1, ih]
  simp only [hconst]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (W 0 / P 0)

end Cochrane.NewKeynesianSelection.SelectionPatches
