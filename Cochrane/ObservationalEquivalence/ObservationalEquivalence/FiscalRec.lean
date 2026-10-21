/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.ForwardSolution
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Scalar debt recursions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.7, pp. 508–509, and
Chapter 23, eqs. (23.1)–(23.4), pp. 512–513: whether fiscal policy is "active" or "passive" is a
statement about the scalar debt recursion `ρ v_{t+1} = (1 − γ) v_t − ΔE_{t+1}π_{t+1} − u_{s,t+1}`.
This module collects the recursion facts used by the rest of the chain.

## Restated from the Woodford Chapter 4 project

Woodford (2003), *Interest and Prices*, Chapter 4, §4, pp. 311–314 (`Fiscal.lean` of the
`NeoWicksellianFramework` project, and `abs_rec_le`, `pow_bounded_eq_zero` of its
`BlanchardKahn` module): the recursion `dRec`, `eq_dRec`; bounded-input-bounded-state for
`|γ| < 1` (`rec_bounded`) and its failure for `|γ| ≥ 1` (`rec_unbounded`); Woodford's (4.2),
(4.4), (4.5) (`Debt42`, `Tax44`, `Debt45`, `debt42_iff_45`) and the definition of a
**locally Ricardian** tax rule with its characterisation `locallyRicardian_iff`
(`|β⁻¹(1 − τ_b)| < 1`) and `ricardian_iff_taub`. This is the boundedness criterion of Leeper
(1991) used to classify fiscal policy.

## General lemmas added here

* `dRec_adapted_of_succ`: the recursion is adapted when the date-`t` input is known at `t + 1`.
* `one_le_abs_one_sub_iff`, `abs_one_sub_lt_one_iff`: `|1 − γ| ≥ 1 ↔ γ ≤ 0 ∨ 2 ≤ γ` and
  `|1 − γ| < 1 ↔ 0 < γ < 2` (the corrected regime boundaries of survey error E12).
* `tendsto_pow_mul_iff`, `eq_zero_of_tendsto_pow_mul`: `qᵀ x → 0 ↔ |q| < 1 ∨ x = 0`.
* `tendsto_zero_of_stable_rec`: a stable recursion `y_{T+1} = q y_T + w_T`, `|q| < 1`, driven by
  geometrically vanishing inputs tends to zero (used for the transversality condition).
* `zero_of_E_succ_eq_smul`: a bounded adapted process with `E_t e_{t+1} = φ e_t`, `|φ| > 1`,
  is identically zero (the active-money uniqueness step).
-/

namespace Cochrane.ObservationalEquivalence.FiscalRec

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Woodford (2003), (4.2)–(4.5): the linearised debt dynamics under a tax rule -/

/-- Woodford (2003), eq. (4.2), p. 312 (restated from the Woodford Chapter 4 project; used for
Cochrane (2023), §22.7, p. 508), with `d_t = b̂_{t−1}`:
`b̂_t = β⁻¹[b̂_{t−1} − b̄ π_t + Ĝ_t − τ̂_t] + b̄ î_t`. -/
def Debt42 (β bb : ℝ) (d π G τ i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • (d t - bb • π t + G t - τ t) + bb • i t

/-- Woodford (2003), eq. (4.4), p. 313 (restated from the Woodford Chapter 4 project; used for
Cochrane (2023), §22.7, p. 508): the linear tax rule
`τ̂_t = τ_b b̂_{t−1} + τ_g Ĝ_t + τ_π π_t + τ_y Ŷ_t + τ_i î_t + v_t`. -/
def Tax44 (τb τg τπ τy τi : ℝ) (d G π Y i v τ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, τ t = τb • d t + τg • G t + τπ • π t + τy • Y t + τi • i t + v t

/-- Woodford (2003), eq. (4.5), p. 313 (restated from the Woodford Chapter 4 project; used for
Cochrane (2023), §22.7, p. 508): the implied law of motion of real debt. -/
def Debt45 (β bb τb τg τπ τy τi : ℝ) (d π G Y i v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
    (bb - β⁻¹ * τi) • i t - β⁻¹ • v t

/-- Woodford (2003), (4.2), (4.4)–(4.5), p. 313 (restated from the Woodford Chapter 4 project;
used for Cochrane (2023), §22.7, p. 508): substituting the tax rule (4.4) into (4.2) gives (4.5). -/
theorem debt42_iff_45 {β bb τb τg τπ τy τi : ℝ} {d π G Y i v τ : ℕ → Ω → ℝ}
    (htax : Tax44 τb τg τπ τy τi d G π Y i v τ) :
    Debt42 β bb d π G τ i ↔ Debt45 β bb τb τg τπ τy τi d π G Y i v := by
  unfold Debt42 Debt45
  refine forall_congr' fun t => ?_
  rw [htax t]
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-! ### The scalar recursion `d_{t+1} = γ d_t + u_t` -/

/-- Woodford (2003), (4.5), p. 313 (restated from the Woodford Chapter 4 project; Cochrane (2023),
(23.4), p. 512): the path generated from `d_0` and inputs `u_t` by `d_{t+1} = γ d_t + u_t`. -/
def dRec (γ : ℝ) (u : ℕ → Ω → ℝ) (d0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d0
  | t + 1 => γ • dRec γ u d0 t + u t

/-- Woodford (2003), (4.5), pp. 313–314 (restated from the Woodford Chapter 4 project; Cochrane
(2023), (23.4), p. 512): a solution of `d_{t+1} = γ d_t + u_t` is determined by `d_0`. -/
theorem eq_dRec {γ : ℝ} {u d : ℕ → Ω → ℝ} (hd : ∀ t, d (t + 1) = γ • d t + u t) :
    d = dRec γ u (d 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [hd t, ih]; rfl

/-- Woodford (2003), p. 277 and Prop. C.2, p. 672 (restated from the Woodford Chapter 4 project;
Cochrane (2023), (23.4), p. 512): a stable scalar recursion `x_{t+1} = λ x_t + u_t`, `|λ| < 1`,
with bounded `u` stays bounded. -/
theorem abs_rec_le {lam C B : ℝ} (hl : |lam| < 1) {u x : ℕ → ℝ} (hu : ∀ t, |u t| ≤ C)
    (hx0 : |x 0| ≤ B) (hx : ∀ t, x (t + 1) = lam * x t + u t) (t : ℕ) :
    |x t| ≤ max B (C / (1 - |lam|)) := by
  have h1 : 0 < 1 - |lam| := by linarith
  induction t with
  | zero => exact le_max_of_le_left hx0
  | succ t ih =>
    rw [hx t]
    set K := max B (C / (1 - |lam|))
    have hK : C ≤ (1 - |lam|) * K := by
      have := le_max_right B (C / (1 - |lam|))
      rw [div_le_iff₀ h1] at this
      linarith
    calc |lam * x t + u t| ≤ |lam| * |x t| + |u t| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |lam| * K + C := by gcongr; exact hu t
      _ ≤ K := by linarith

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): for `|γ| < 1` the recursion `d_{t+1} = γ d_t + u_t` is
bounded-input-bounded-state: `|d_t| ≤ B + U/(1 − |γ|)`. -/
theorem rec_bounded {γ B U : ℝ} (hγ : |γ| < 1) {u d : ℕ → Ω → ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hu : ∀ t ω, |u t ω| ≤ U) (hd : ∀ t, d (t + 1) = γ • d t + u t) (h0 : ∀ ω, |d 0 ω| ≤ B) :
    ∀ t ω, |d t ω| ≤ B + U / (1 - |γ|) := by
  intro t ω
  have hq : 0 ≤ U / (1 - |γ|) := div_nonneg hU (by linarith)
  refine (abs_rec_le hγ (u := fun t => u t ω) (x := fun t => d t ω) (fun t => hu t ω) (h0 ω)
    (fun t => by simp [hd t]) t).trans ?_
  exact max_le (by linarith) (by linarith)

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): for `|γ| ≥ 1` the recursion is not bounded-input-bounded-state: with
`s = sign γ` and inputs `u_t = ε s^{t+1}`, the path from `d_0 = 0` satisfies `|d_t| ≥ ε t`. -/
theorem rec_unbounded {γ ε : ℝ} (hγ : 1 ≤ |γ|) (hε : 0 ≤ ε) {d : ℕ → Ω → ℝ}
    (hd : ∀ t, d (t + 1) = γ • d t +
      fun _ => ε * (if 0 ≤ γ then (1 : ℝ) else -1) ^ (t + 1))
    (h0 : d 0 = 0) : ∀ t ω, ε * t ≤ |d t ω| := by
  set s : ℝ := if 0 ≤ γ then 1 else -1 with hs
  have hss : s * s = 1 := by rw [hs]; split_ifs <;> norm_num
  have hγs : γ = s * |γ| := by
    rw [hs]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have key : ∀ t ω, ε * t ≤ s ^ t * d t ω := by
    intro t
    induction t with
    | zero => intro ω; simp [h0]
    | succ t ih =>
      intro ω
      rw [hd t]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : s ^ (t + 1) * (γ * d t ω + ε * s ^ (t + 1)) = |γ| * (s ^ t * d t ω) + ε := by
        have h2 : s ^ (t + 1) * s ^ (t + 1) = 1 := by
          rw [← mul_pow, hss, one_pow]
        have h3 : γ * d t ω = s * |γ| * d t ω := by rw [← hγs]
        rw [h3]
        calc s ^ (t + 1) * (s * |γ| * d t ω + ε * s ^ (t + 1))
            = |γ| * (s ^ t * (s * s) * d t ω) + ε * (s ^ (t + 1) * s ^ (t + 1)) := by ring
          _ = _ := by rw [hss, h2]; ring
      rw [e]
      push_cast
      have := ih ω
      have ht : 0 ≤ ε * t := mul_nonneg hε (Nat.cast_nonneg t)
      nlinarith
  intro t ω
  have hst : |s ^ t| = 1 := by
    rw [abs_pow]
    have : |s| = 1 := by rw [hs]; split_ifs <;> norm_num
    rw [this, one_pow]
  calc ε * t ≤ s ^ t * d t ω := key t ω
    _ ≤ |s ^ t * d t ω| := le_abs_self _
    _ = |d t ω| := by rw [abs_mul, hst, one_mul]

/-- Woodford (2003), p. 314 and App. C.8 (restated from the Woodford Chapter 4 project; Cochrane
(2023), §22.7, p. 508): if `|γ| > 1` and `γᵗ e₀` stays bounded, then `e₀ = 0`. -/
theorem pow_bounded_eq_zero {γ e0 M : ℝ} (hγ : 1 < |γ|) (h : ∀ t : ℕ, |γ ^ t * e0| ≤ M) :
    e0 = 0 := by
  by_contra hne
  have hpos : 0 < |e0| := abs_pos.mpr hne
  have ht := tendsto_pow_atTop_atTop_of_one_lt hγ
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop (M / |e0|)).exists
  have := h n
  rw [abs_mul, abs_pow, div_lt_iff₀ hpos] at *
  linarith

/-- Woodford (2003), App. C.8, p. 685 (restated from the Woodford Chapter 4 project; Cochrane
(2023), (23.4), p. 512): the recursion driven by adapted inputs from a constant start is
adapted. -/
theorem dRec_adapted {γ b0 : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    𝔼.Adapted (dRec γ u (fun _ => b0)) := by
  intro t
  induction t with
  | zero => exact 𝔼.const 0 b0
  | succ t ih =>
    change 𝔼.E (t + 1) (γ • dRec γ u (fun _ => b0) t + u t) = γ • dRec γ u (fun _ => b0) t + u t
    rw [map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu t)]

/-- Cochrane (2023), (23.4), p. 512 (debt `v_{t+1}` depends on date-`t+1` inflation): the
recursion `d_{t+1} = γ d_t + u_t` is adapted when `d_0` is known at date 0 and the input `u_t`
is known at date `t + 1`. -/
theorem dRec_adapted_of_succ {γ : ℝ} {u : ℕ → Ω → ℝ} {d0 : Ω → ℝ} (h0 : 𝔼.E 0 d0 = d0)
    (hu : ∀ t, 𝔼.E (t + 1) (u t) = u t) : 𝔼.Adapted (dRec γ u d0) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    change 𝔼.E (t + 1) (γ • dRec γ u d0 t + u t) = γ • dRec γ u d0 t + u t
    rw [map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih, hu t]

/-! ### Locally Ricardian tax rules (the boundedness criterion) -/

/-- Woodford (2003), p. 312 (restated from the Woodford Chapter 4 project; the boundedness
criterion for passive fiscal policy, Cochrane (2023), §22.7, p. 508): a tax rule is **locally
Ricardian** if, substituted into (4.5), it keeps real debt bounded for every small initial debt
and all small paths of `π`, `Ŷ`, `î`, `Ĝ`, `v`. -/
def LocallyRicardian (Ω : Type*) (β bb τb τg τπ τy τi : ℝ) : Prop :=
  ∃ δ > 0, ∀ (b0 : ℝ) (d π Y i G v : ℕ → Ω → ℝ), |b0| ≤ δ →
    (∀ t ω, |π t ω| ≤ δ ∧ |Y t ω| ≤ δ ∧ |i t ω| ≤ δ ∧ |G t ω| ≤ δ ∧ |v t ω| ≤ δ) →
    d 0 = (fun _ => b0) → Debt45 β bb τb τg τπ τy τi d π G Y i v → BoundedProc d

/-- Woodford (2003), p. 313 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): a tax rule (4.4) is locally Ricardian iff `|β⁻¹(1 − τ_b)| < 1`. -/
theorem locallyRicardian_iff [Nonempty Ω] {β bb τb τg τπ τy τi : ℝ} (hβ : 0 < β) :
    LocallyRicardian Ω β bb τb τg τπ τy τi ↔ |β⁻¹ * (1 - τb)| < 1 := by
  set γ := β⁻¹ * (1 - τb) with hγ
  constructor
  · intro hR
    by_contra hcon
    have h1 : 1 ≤ |γ| := not_lt.mp hcon
    obtain ⟨δ, hδ, hR⟩ := hR
    set ε := δ / (1 + β) with hε
    have hε0 : 0 < ε := div_pos hδ (by linarith)
    have hεβ : β * ε ≤ δ := by
      rw [hε, mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    set s : ℝ := if 0 ≤ γ then 1 else -1 with hs
    have habs : ∀ n : ℕ, |s ^ n| = 1 := by
      intro n; rw [abs_pow]
      have : |s| = 1 := by rw [hs]; split_ifs <;> norm_num
      rw [this, one_pow]
    set u : ℕ → Ω → ℝ := fun t _ => ε * s ^ (t + 1) with hu
    set d := dRec γ u 0 with hd
    have hrec : ∀ t, d (t + 1) = γ • d t + u t := fun t => rfl
    have hB := hR 0 d 0 0 0 0 (fun t _ => -(β * ε * s ^ (t + 1))) (by simp [hδ.le])
      (fun t ω => by
        refine ⟨by simp [hδ.le], by simp [hδ.le], by simp [hδ.le], by simp [hδ.le], ?_⟩
        rw [abs_neg, abs_mul, habs, mul_one, abs_of_pos (mul_pos hβ hε0)]
        exact hεβ)
      (by funext ω; rfl) (fun t => by
        rw [hrec t]
        funext ω
        simp only [hu, hγ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
          smul_eq_mul]
        field_simp
        ring)
    obtain ⟨M, hM⟩ := hB
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have hgrow := rec_unbounded h1 hε0.le (d := d) (fun t => hrec t) rfl
    obtain ⟨n, hn⟩ := exists_nat_gt (M / ε)
    have := hgrow n ω
    have := hM n ω
    rw [div_lt_iff₀ hε0] at hn
    linarith
  · intro hγ1
    refine ⟨1, one_pos, fun b0 d π Y i G v hb0 hin hd0 hd => ?_⟩
    set U := β⁻¹ * (|bb + τπ| + |1 - τg| + |τy|) + |bb - β⁻¹ * τi| + β⁻¹ with hU
    have hβi : 0 < β⁻¹ := inv_pos.mpr hβ
    have hU0 : 0 ≤ U := by positivity
    set u : ℕ → Ω → ℝ := fun t => β⁻¹ • (-(bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
      (bb - β⁻¹ * τi) • i t - β⁻¹ • v t with hu
    have hrec : ∀ t, d (t + 1) = γ • d t + u t := by
      intro t
      rw [hd t]
      funext ω
      simp only [hu, hγ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hub : ∀ t ω, |u t ω| ≤ U := by
      intro t ω
      obtain ⟨a1, a2, a3, a4, a5⟩ := hin t ω
      simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have q1 : |-(bb + τπ) * π t ω + (1 - τg) * G t ω - τy * Y t ω| ≤
          |bb + τπ| + |1 - τg| + |τy| := by
        refine (abs_sub _ _).trans ?_
        refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_neg]
        nlinarith [abs_nonneg (bb + τπ), abs_nonneg (1 - τg), abs_nonneg τy,
          mul_le_mul_of_nonneg_left a1 (abs_nonneg (bb + τπ)),
          mul_le_mul_of_nonneg_left a4 (abs_nonneg (1 - τg)),
          mul_le_mul_of_nonneg_left a2 (abs_nonneg τy)]
      refine (abs_sub _ _).trans ?_
      refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβi]
      nlinarith [mul_le_mul_of_nonneg_left q1 hβi.le,
        mul_le_mul_of_nonneg_left a3 (abs_nonneg (bb - β⁻¹ * τi)),
        mul_le_mul_of_nonneg_left a5 hβi.le]
    exact ⟨1 + U / (1 - |γ|), rec_bounded hγ1 zero_le_one hU0 hub hrec
      (fun ω => by rw [hd0]; simpa using hb0)⟩

/-- Woodford (2003), p. 314 (restated from the Woodford Chapter 4 project; Cochrane (2023),
§22.7, p. 508): for `0 < β` and `τ_b ≤ 1`, `|β⁻¹(1 − τ_b)| < 1` iff `τ_b > 1 − β`. -/
theorem ricardian_iff_taub {β τb : ℝ} (hβ : 0 < β) (hτ : τb ≤ 1) :
    |β⁻¹ * (1 - τb)| < 1 ↔ 1 - β < τb := by
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hβ.le) (by linarith)), ← div_eq_inv_mul,
    div_lt_one hβ]
  constructor <;> intro h <;> linarith

/-! ### Regime boundaries -/

/-- Cochrane (2023), pp. 495, 501, 512 (survey error E12): fiscal policy is active under the
transversality criterion, `|1 − γ| ≥ 1`, exactly when `γ ≤ 0` or `γ ≥ 2`. -/
theorem one_le_abs_one_sub_iff (γ : ℝ) : 1 ≤ |1 - γ| ↔ γ ≤ 0 ∨ 2 ≤ γ := by
  constructor
  · intro h
    rcases le_abs'.mp h with h1 | h1
    · right; linarith
    · left; linarith
  · rintro (h | h)
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith

/-- Cochrane (2023), pp. 512–513 (survey error E12): `|1 − γ| < 1` exactly when `0 < γ < 2`. -/
theorem abs_one_sub_lt_one_iff (γ : ℝ) : |1 - γ| < 1 ↔ 0 < γ ∧ γ < 2 := by
  rw [abs_sub_lt_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ### Limits of geometric sequences -/

/-- Cochrane (2023), p. 513 (the transversality condition on `qᵀ x`): `qᵀ x → 0` iff
`|q| < 1` or `x = 0`. -/
theorem tendsto_pow_mul_iff (q x : ℝ) :
    Tendsto (fun T : ℕ => q ^ T * x) atTop (𝓝 0) ↔ |q| < 1 ∨ x = 0 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨hq, hx⟩ := hc
    have hb : ∀ T : ℕ, |x| ≤ |q ^ T * x| := fun T => by
      rw [abs_mul, abs_pow]
      exact le_mul_of_one_le_left (abs_nonneg x) (one_le_pow₀ hq)
    have h0 : Tendsto (fun T : ℕ => |q ^ T * x|) atTop (𝓝 0) := by
      simpa using h.abs
    have : |x| ≤ 0 := ge_of_tendsto' h0 hb
    exact hx (abs_nonpos_iff.mp this)
  · rintro (h | h)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).mul_const x
    · simp [h]

/-- Cochrane (2023), p. 513 ("only one value … keeps debt from exploding"): if `|q| ≥ 1` and
`qᵀ x → 0` then `x = 0`. -/
theorem eq_zero_of_tendsto_pow_mul {q x : ℝ} (hq : 1 ≤ |q|)
    (h : Tendsto (fun T : ℕ => q ^ T * x) atTop (𝓝 0)) : x = 0 := by
  rcases (tendsto_pow_mul_iff q x).mp h with h1 | h1
  · linarith
  · exact h1

/-- Cochrane (2023), p. 513 (debt growing more slowly than the interest rate is consistent with
the transversality condition): a stable recursion `y_{T+1} = q y_T + w_T` with `|q| < 1` and
geometrically vanishing inputs `|w_T| ≤ C rᵀ`, `0 ≤ r < 1`, tends to zero. -/
theorem tendsto_zero_of_stable_rec {q r C : ℝ} (hq : |q| < 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {y w : ℕ → ℝ} (hw : ∀ T, |w T| ≤ C * r ^ T) (hy : ∀ T, y (T + 1) = q * y T + w T) :
    Tendsto y atTop (𝓝 0) := by
  set R := max |q| r with hR
  have hR0 : 0 ≤ R := le_max_of_le_right hr0
  have hR1 : R < 1 := max_lt hq hr1
  have hC : 0 ≤ C := by
    have := (abs_nonneg (w 0)).trans (hw 0)
    simpa using this
  have hbound : ∀ T, |y T| ≤ R ^ T * |y 0| + C * T * R ^ (T - 1) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [hy T]
      have hqR : |q| ≤ R := le_max_left _ _
      have hrR : r ^ T ≤ R ^ T := pow_le_pow_left₀ hr0 (le_max_right _ _) T
      have h1 : |q * y T + w T| ≤ R * |y T| + C * R ^ T := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ((hw T).trans ?_))
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right hqR (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left hrR hC
      refine h1.trans ?_
      have h2 : R * |y T| ≤ R * (R ^ T * |y 0| + C * T * R ^ (T - 1)) :=
        mul_le_mul_of_nonneg_left ih hR0
      rcases T with _ | T
      · simp only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero, zero_tsub] at h2 ⊢
        push_cast
        nlinarith
      · simp only [Nat.add_sub_cancel] at h2 ⊢
        push_cast at h2 ⊢
        have e : R * (R ^ (T + 1) * |y 0| + C * (T + 1) * R ^ T) + C * R ^ (T + 1) =
            R ^ (T + 1 + 1) * |y 0| + C * (T + 1 + 1) * R ^ (T + 1) := by ring
        linarith
  have hlim1 : Tendsto (fun T : ℕ => R ^ T * |y 0|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1).mul_const |y 0|
  have hlim2 : Tendsto (fun T : ℕ => C * T * R ^ (T - 1)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have h1 : Tendsto (fun T : ℕ => (T : ℝ) * R ^ T + R ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_self_mul_const_pow_of_lt_one hR0 hR1).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hR0 hR1)
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    refine h2.congr fun T => ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun T => norm_nonneg _) (fun T => ?_) (by simpa using hlim1.add hlim2)
  rw [sub_zero, Real.norm_eq_abs]
  exact hbound T

/-! ### Active money: bounded solutions of `E_t e_{t+1} = φ e_t` -/

/-- Cochrane (2023), (22.1), p. 495, and (16.19), p. 371 (active money, `|φ| > 1`): a bounded
process with `E_t e_{t+1} = φ e_t` is identically zero. -/
theorem zero_of_E_succ_eq_smul {φ : ℝ} (hφ : 1 < |φ|) {e : ℕ → Ω → ℝ}
    (hb : BoundedProc e) (he : ∀ t, 𝔼.E t (e (t + 1)) = φ • e t) : e = 0 := by
  have hφ0 : φ ≠ 0 := by
    intro h; rw [h, abs_zero] at hφ; linarith
  have hinv : |φ⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hφ
  refine 𝔼.forward_unique hinv (u := 0) (fun t => ?_) (fun t => ?_) hb ⟨0, fun _ _ => by simp⟩
  · rw [he t, smul_smul, inv_mul_cancel₀ hφ0, one_smul, Pi.zero_apply, add_zero]
  · simp

end Cochrane.ObservationalEquivalence.FiscalRec
