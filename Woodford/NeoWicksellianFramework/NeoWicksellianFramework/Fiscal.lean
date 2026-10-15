/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Money
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Fiscal requirements for price stability

Woodford (2003), *Interest and Prices*, Chapter 4, §4, pp. 311–319, and App. C.8, pp. 685–686.

## The budget constraint and locally Ricardian rules

* (4.1): `Budget`, `budget_real` (`b_t = (1 + i_t)(b_{t−1}/Π_t + G_t − τ_t)`); the steady state
  `steadyState_iff` (`τ̄ = Ḡ + (1 − β)B̄`).
* (4.2) as an exact derivative: `debtMap`, `hasFDerivAt_debtMap`.
* (4.2), (4.4), (4.5): `Debt42`, `Tax44`, `Debt45`, `debt42_iff_45`.
* Locally Ricardian (p. 312): `LocallyRicardian`; `locallyRicardian_iff` (iff
  `|β⁻¹(1 − τ_b)| < 1`, both directions, via the scalar bounded-input-bounded-state facts
  `dRec`, `eq_dRec`, `rec_bounded`, `rec_unbounded`); `ricardian_iff_taub` (iff `τ_b > 1 − β`
  when `τ_b ≤ 1`).

## Proposition 4.11 (App. C.8), proved in full

The book adjoins (4.5) to the system of Proposition 4.3 and appeals to a Blanchard–Kahn count
for a `3 × 3` system with one predetermined variable. Here that system is `Eq3` (two
non-predetermined variables `z_t = A E_t z_{t+1} + w_t`, debt `d_{t+1} = γ d_t + c·z_t + f_t`)
and everything needed is proved:

* E29: the stacked matrix is block lower-triangular, not block-diagonal
  (`stacked_blockDiagonal_iff`); its eigenvalues are still those of `A` and `γ`
  (`stacked_charpoly`).
* `|γ| < 1` (Ricardian): `determinate3_ricardian` (determinate iff `A` is Schur–Cohn; the
  unique `z` is the forward solution (2.34)), `not_zeroDet_ricardian`.
* `|γ| > 1` and `A` Schur–Cohn (non-Ricardian + Taylor principle): `nonricardian_TP_initial`,
  `nonricardian_TP_shock` (at most one initial debt / date-0 shock admits a bounded solution),
  `not_zeroDet_nonricardian_TP`, `not_determinate3_nonricardian_TP`.
* `|γ| > 1` and real roots `|λ₁| < 1 < |λ₂|` (non-Ricardian, Taylor principle violated): the
  book's claim needs the **non-degeneracy `c·r₂ ≠ 0`** — the debt equation must load on the
  eigenvector `r₂` of the root `λ₂` (the direction of the self-fulfilling solutions that make the
  `2 × 2` block indeterminate). Under it: `unique3_spectral`, `exists3_spectral`,
  `determinate3_spectral`; without it: `not_zeroDet_degenerate`, `not_determinate3_degenerate`
  (tools: `dot2`, `Spectral`, `proj`, `proj_solves`, `left_eigen`, `recon`, `solves_of_proj`,
  `proj_bounded_adapted`, `lvec`, `rvec`, `spectral_of_roots`, `rvec_eigen`, `nondeg_iff`).
* The model of §4 (`Eq411`, `cvec411`, `f411`, `eq411_iff`, `Determinate411`,
  `determinate411_of`, `zeroDet_of_determinate411`, `taylorB_roots`, `lamPlus`, `lamMinus`,
  `one_lt_gamma`):
  `prop411_ricardian` (determinate iff (2.7)), `prop411_ricardian_indeterminate`;
  `prop411_nonricardian_TP`, `prop411_nonricardian_TP_initial`,
  `prop411_nonricardian_TP_shock`; `prop411_nonricardian_noTP` (determinate **iff**
  `c_π a₀₁ + c_x(λ₂ − a₀₀) ≠ 0`) and the counterexample `prop411_printed_fails` (a
  non-Ricardian rule violating the Taylor principle with an indeterminate equilibrium).

The `2 × 2` determinacy theory (`BlanchardKahn.fwd_existsUnique`, `fwdDeterminate_iff`) and
Proposition 4.3's model and matrix (`Determinacy2.TaylorEqm`, `taylorB`,
`taylorB_schurStable_iff`, `taylorEqm_iff_solves`) are imported through the `Money` module of
this chain. Boundary cases of (2.7) (equality) are excluded, as in the book ("generically").
-/

namespace Woodford.NeoWicksellianFramework.Fiscal

open Filter Topology
open Woodford.NeoWicksellianFramework.Money Determinacy2 BlanchardKahn
open BasicModel (xbar)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (4.1)–(4.2): the government's flow budget constraint -/

/-- Woodford (2003), eq. (4.1), p. 311: `D_t = (1 + i_{t−1}) D_{t−1} + (P_t G_t − T_t)`
(deterministic paths; the identity holds state by state). -/
def Budget (D i P G T : ℕ → ℝ) : Prop :=
  ∀ t, D (t + 1) = (1 + i t) * D t + (P (t + 1) * G (t + 1) - T (t + 1))

/-- Woodford (2003), p. 312: in terms of the maturity value of real debt
`b_t = (1 + i_t) D_t/P_t`, real taxes `τ_t = T_t/P_t` and gross inflation `Π_t = P_t/P_{t−1}`,
(4.1) is `b_t = (1 + i_t)(b_{t−1}/Π_t + G_t − τ_t)`. -/
theorem budget_real {D i P G T : ℕ → ℝ} (hP : ∀ t, 0 < P t) (h : Budget D i P G T) (t : ℕ) :
    (1 + i (t + 1)) * D (t + 1) / P (t + 1) = (1 + i (t + 1)) *
      (((1 + i t) * D t / P t) / (P (t + 1) / P t) + G (t + 1) - T (t + 1) / P (t + 1)) := by
  rw [h t]
  have h1 := hP t
  have h2 := hP (t + 1)
  field_simp
  ring

/-- Woodford (2003), p. 312: a steady state with zero inflation, `i = ī = β⁻¹ − 1`, constant
real debt `B̄` and taxes `τ̄`, satisfies (4.1) iff `τ̄ = Ḡ + (1 − β) B̄` (`β > 0`). -/
theorem steadyState_iff {β Bbar Gbar τbar : ℝ} (hβ : 0 < β) :
    Bbar = β⁻¹ * (Bbar / 1 + Gbar - τbar) ↔ τbar = Gbar + (1 - β) * Bbar := by
  rw [div_one]
  constructor
  · intro h
    have h' := congrArg (fun y => β * y) h
    rw [← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul] at h'
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), (4.2), p. 312: the maturity value of real debt as a function of the
deviations `(b̂_{t−1}, π_t, Ĝ_t, τ̂_t, î_t)`, in units of `Ȳ`:
`b̂_t = [β⁻¹ e^{î}((B̄ + Ȳ b̂_{t−1}) e^{−π} + Ḡ + Ȳ Ĝ − τ̄ − Ȳ τ̂) − B̄]/Ȳ`, using
`1 + i = β⁻¹ e^{î}`, `1/Π = e^{−π}`, `b = B̄ + Ȳ b̂`, `G = Ḡ + Ȳ Ĝ`, `τ = τ̄ + Ȳ τ̂`. -/
noncomputable def debtMap (β Bbar Gbar τbar Ybar : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  (β⁻¹ * Real.exp (v 4) * ((Bbar + Ybar * v 0) * Real.exp (-v 1) + Gbar + Ybar * v 2 - τbar -
    Ybar * v 3) - Bbar) / Ybar

/-- Woodford (2003), eq. (4.2), p. 312 (exact derivative): at the steady state
(`τ̄ = Ḡ + (1 − β)B̄`, `Ȳ ≠ 0`, `β ≠ 0`) the derivative of `debtMap` is
`β⁻¹[b̂_{t−1} − b̄ π_t + Ĝ_t − τ̂_t] + b̄ î_t` with `b̄ = B̄/Ȳ`. -/
theorem hasFDerivAt_debtMap {β Bbar Gbar τbar Ybar : ℝ} (hβ : β ≠ 0) (hY : Ybar ≠ 0)
    (hss : τbar = Gbar + (1 - β) * Bbar) :
    ∃ D : (Fin 5 → ℝ) →L[ℝ] ℝ, HasFDerivAt (debtMap β Bbar Gbar τbar Ybar) D 0 ∧
      ∀ v, D v = β⁻¹ * (v 0 - Bbar / Ybar * v 1 + v 2 - v 3) + Bbar / Ybar * v 4 := by
  have p : ∀ i : Fin 5, HasFDerivAt (fun v : Fin 5 → ℝ => v i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) i) 0 :=
    fun i => hasFDerivAt_apply i 0
  have h1 := ((p 0).const_mul Ybar).const_add Bbar
  have h2 := (p 1).neg.exp
  have h3 := (((((h1.mul h2).add_const Gbar).add ((p 2).const_mul Ybar)).sub_const τbar).sub
    ((p 3).const_mul Ybar))
  have h4 := ((p 4).exp.const_mul β⁻¹).mul h3
  have h5 := (h4.sub_const Bbar).mul_const Ybar⁻¹
  have h6 := h5.congr_of_eventuallyEq (f₁ := debtMap β Bbar Gbar τbar Ybar)
    (Filter.Eventually.of_forall fun v => by
      simp only [debtMap, div_eq_mul_inv, Pi.mul_apply, Pi.neg_apply, Pi.sub_apply,
        Pi.add_apply])
  refine ⟨_, h6, fun v => ?_⟩
  · simp only [Pi.zero_apply, Real.exp_zero, mul_one, mul_zero, add_zero, Fin.isValue,
      Pi.neg_apply, neg_zero, smul_neg, one_smul, Pi.mul_apply, Pi.add_apply, Pi.sub_apply,
      sub_zero, smul_add, add_apply, smul_apply, sub_apply, neg_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hss]
    field_simp
    ring

/-! ### (4.2)–(4.5): the linearised debt dynamics under a tax rule -/

/-- Woodford (2003), eq. (4.2), p. 312, with `d_t = b̂_{t−1}` (so `d_0 = b̂_{−1}` is the
initial debt): `b̂_t = β⁻¹[b̂_{t−1} − b̄ π_t + Ĝ_t − τ̂_t] + b̄ î_t`. -/
def Debt42 (β bb : ℝ) (d π G τ i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • (d t - bb • π t + G t - τ t) + bb • i t

/-- Woodford (2003), eq. (4.4), p. 313: the linear tax rule
`τ̂_t = τ_b b̂_{t−1} + τ_g Ĝ_t + τ_π π_t + τ_y Ŷ_t + τ_i î_t + v_t`. -/
def Tax44 (τb τg τπ τy τi : ℝ) (d G π Y i v τ : ℕ → Ω → ℝ) : Prop :=
  ∀ t, τ t = τb • d t + τg • G t + τπ • π t + τy • Y t + τi • i t + v t

/-- Woodford (2003), eq. (4.5), p. 313: the implied law of motion of real debt,
`b̂_t = β⁻¹[(1 − τ_b) b̂_{t−1} − (b̄ + τ_π) π_t + (1 − τ_g) Ĝ_t − τ_y Ŷ_t]
+ (b̄ − β⁻¹τ_i) î_t − β⁻¹ v_t`. -/
def Debt45 (β bb τb τg τπ τy τi : ℝ) (d π G Y i v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
    (bb - β⁻¹ * τi) • i t - β⁻¹ • v t

/-- Woodford (2003), (4.2), (4.4)–(4.5), p. 313: substituting the tax rule (4.4) into (4.2)
gives exactly (4.5). -/
theorem debt42_iff_45 {β bb τb τg τπ τy τi : ℝ} {d π G Y i v τ : ℕ → Ω → ℝ}
    (htax : Tax44 τb τg τπ τy τi d G π Y i v τ) :
    Debt42 β bb d π G τ i ↔ Debt45 β bb τb τg τπ τy τi d π G Y i v := by
  unfold Debt42 Debt45
  refine forall_congr' fun t => ?_
  rw [htax t]
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Woodford (2003), (4.5), p. 313: the debt path generated recursively from the initial debt
`d_0` and the inputs `u_t`: `d_{t+1} = γ d_t + u_t`. -/
def dRec (γ : ℝ) (u : ℕ → Ω → ℝ) (d0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d0
  | t + 1 => γ • dRec γ u d0 t + u t

/-- Woodford (2003), (4.5), pp. 313–314: a solution of `d_{t+1} = γ d_t + u_t` is determined by
`d_0`: it is `dRec`. -/
theorem eq_dRec {γ : ℝ} {u d : ℕ → Ω → ℝ} (hd : ∀ t, d (t + 1) = γ • d t + u t) :
    d = dRec γ u (d 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [hd t, ih]; rfl

/-- Woodford (2003), pp. 313–314: for `|γ| < 1` the scalar recursion `d_{t+1} = γ d_t + u_t` is
bounded-input-bounded-state: `|d_t| ≤ B + U/(1 − |γ|)` when `|d_0| ≤ B`, `|u| ≤ U`. -/
theorem rec_bounded {γ B U : ℝ} (hγ : |γ| < 1) {u d : ℕ → Ω → ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hu : ∀ t ω, |u t ω| ≤ U) (hd : ∀ t, d (t + 1) = γ • d t + u t) (h0 : ∀ ω, |d 0 ω| ≤ B) :
    ∀ t ω, |d t ω| ≤ B + U / (1 - |γ|) := by
  intro t ω
  have hq : 0 ≤ U / (1 - |γ|) := div_nonneg hU (by linarith)
  refine (abs_rec_le hγ (u := fun t => u t ω) (x := fun t => d t ω) (fun t => hu t ω) (h0 ω)
    (fun t => by simp [hd t]) t).trans ?_
  exact max_le (by linarith) (by linarith)

/-- Woodford (2003), pp. 313–314: for `|γ| ≥ 1` the scalar recursion is not
bounded-input-bounded-state: with `s = sign γ` and inputs `u_t = ε s^{t+1}` (`|u_t| = ε`), the
path from `d_0 = 0` satisfies `|d_t| ≥ ε t`. -/
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

/-- Woodford (2003), p. 312: a tax rule is **locally Ricardian** if, substituted into the
budget constraint ((4.5)), it keeps real debt bounded for every initial debt and all paths of
`π`, `Ŷ`, `î` and of the disturbances `Ĝ`, `v` within some (small) bound `δ`. -/
def LocallyRicardian (Ω : Type*) (β bb τb τg τπ τy τi : ℝ) : Prop :=
  ∃ δ > 0, ∀ (b0 : ℝ) (d π Y i G v : ℕ → Ω → ℝ), |b0| ≤ δ →
    (∀ t ω, |π t ω| ≤ δ ∧ |Y t ω| ≤ δ ∧ |i t ω| ≤ δ ∧ |G t ω| ≤ δ ∧ |v t ω| ≤ δ) →
    d 0 = (fun _ => b0) → Debt45 β bb τb τg τπ τy τi d π G Y i v → BoundedProc d

/-- Woodford (2003), p. 313: a tax rule (4.4) is locally Ricardian iff `|β⁻¹(1 − τ_b)| < 1`
(both directions: bounded-input-bounded-state for the scalar recursion (4.5); the fiscal shock
`v` alone can excite every input sequence). -/
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
    have hεδ : ε ≤ δ := by
      rw [hε, div_le_iff₀ (by linarith)]; nlinarith
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

/-- Woodford (2003), p. 314: for `0 < β` and `τ_b ≤ 1` (end-of-period debt weakly increasing in
beginning-of-period debt), `|β⁻¹(1 − τ_b)| < 1` iff `τ_b > 1 − β`. -/
theorem ricardian_iff_taub {β τb : ℝ} (hβ : 0 < β) (hτ : τb ≤ 1) :
    |β⁻¹ * (1 - τb)| < 1 ↔ 1 - β < τb := by
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hβ.le) (by linarith)), ← div_eq_inv_mul,
    div_lt_one hβ]
  constructor <;> intro h <;> linarith

/-! ### App. C.8: the stacked system with one predetermined variable -/

/-- Woodford (2003), App. C.8, p. 685: the stacked system — the two non-predetermined
variables `z_t` solve `z_t = A E_t z_{t+1} + w_t`, and debt `d_t = b̂_{t−1}` (predetermined,
`d_0 = b̂_{−1}` given) follows `d_{t+1} = γ d_t + c·z_t + f_t`. -/
def Eq3 (A : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) (γ : ℝ) (w : ℕ → Fin 2 → Ω → ℝ)
    (f : ℕ → Ω → ℝ) (b0 : ℝ) (z : ℕ → Fin 2 → Ω → ℝ) (d : ℕ → Ω → ℝ) : Prop :=
  𝔼.Solves A w z ∧ d 0 = (fun _ => b0) ∧
    ∀ t, d (t + 1) = γ • d t + (c 0 • z t 0 + c 1 • z t 1 + f t)

/-- Woodford (2003), p. 314 (determinacy à la Leeper): for all bounded adapted disturbances and
every initial debt there is exactly one bounded adapted solution of the stacked system. -/
def Determinate3 (A : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) (γ : ℝ) : Prop :=
  ∀ (w : ℕ → Fin 2 → Ω → ℝ) (f : ℕ → Ω → ℝ) (b0 : ℝ), BoundedVec w → 𝔼.AdaptedVec w →
    BoundedProc f → 𝔼.Adapted f →
    ∃! p : (ℕ → Fin 2 → Ω → ℝ) × (ℕ → Ω → ℝ), Eq3 𝔼 A c γ w f b0 p.1 p.2 ∧
      𝔼.AdaptedVec p.1 ∧ BoundedVec p.1 ∧ 𝔼.Adapted p.2 ∧ BoundedProc p.2

/-- Woodford (2003), p. 314: determinacy for the undisturbed system — for every initial debt
exactly one bounded adapted solution with `w = 0`, `f = 0` (implied by `Determinate3`). -/
def ZeroDet (A : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) (γ : ℝ) : Prop :=
  ∀ b0 : ℝ, ∃! p : (ℕ → Fin 2 → Ω → ℝ) × (ℕ → Ω → ℝ), Eq3 𝔼 A c γ 0 0 b0 p.1 p.2 ∧
    𝔼.AdaptedVec p.1 ∧ BoundedVec p.1 ∧ 𝔼.Adapted p.2 ∧ BoundedProc p.2

/-- Woodford (2003), p. 314: determinacy implies determinacy without disturbances. -/
theorem zeroDet_of_determinate3 {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ} {γ : ℝ}
    (h : Determinate3 𝔼 A c γ) : ZeroDet 𝔼 A c γ := fun b0 =>
  h 0 0 b0 ⟨0, fun t i ω => by simp⟩ (fun t i => by simp) ⟨0, fun t ω => by simp⟩
    (fun t => by simp)

/-- Woodford (2003), App. C.8, p. 685: the coupling `c·z_t + f_t` of a bounded adapted state. -/
theorem coupling_bounded_adapted (c : Fin 2 → ℝ) {z : ℕ → Fin 2 → Ω → ℝ} {f : ℕ → Ω → ℝ}
    (hz : BoundedVec z) (haz : 𝔼.AdaptedVec z) (hf : BoundedProc f) (haf : 𝔼.Adapted f) :
    BoundedProc (fun t => c 0 • z t 0 + c 1 • z t 1 + f t) ∧
      𝔼.Adapted (fun t => c 0 • z t 0 + c 1 • z t 1 + f t) := by
  obtain ⟨M, hM⟩ := hz
  obtain ⟨K, hK⟩ := hf
  refine ⟨⟨|c 0| * M + |c 1| * M + K, fun t ω => ?_⟩, fun t => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) (hK t ω))
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hM t 0 ω) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hM t 1 ω) (abs_nonneg _))
  · simp only [map_add, map_smul, haz t 0, haz t 1, haf t]

/-- Woodford (2003), App. C.8, p. 685: the debt path `dRec` driven by adapted inputs from a
constant initial value is adapted (indeed `d_{t+1}` is known at `t`). -/
theorem dRec_adapted {γ b0 : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    𝔼.Adapted (dRec γ u (fun _ => b0)) := by
  intro t
  induction t with
  | zero => exact 𝔼.const 0 b0
  | succ t ih =>
    change 𝔼.E (t + 1) (γ • dRec γ u (fun _ => b0) t + u t) = γ • dRec γ u (fun _ => b0) t + u t
    rw [map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu t)]

/-- **Proposition 4.11, Ricardian case, indeterminacy** (Woodford (2003), App. C.8,
p. 686): if `|γ| < 1` and `A` fails the Schur–Cohn condition, already the undisturbed system has
two bounded solutions (a self-fulfilling path for `z`, with bounded debt). -/
theorem not_zeroDet_ricardian [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ}
    {γ : ℝ} (hγ : |γ| < 1) (hA : ¬ SchurStable (tr2 A) (det2 A)) : ¬ ZeroDet 𝔼 A c γ := by
  intro hdet
  have hz : 𝔼.Solves A 0 0 := fun t i => by simp
  obtain ⟨y, hy, hay, hby, hne⟩ :=
    𝔼.system_not_unique hA hz (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  obtain ⟨⟨bu, hbu⟩, hau⟩ := coupling_bounded_adapted 𝔼 c hby hay
    (f := 0) ⟨0, fun t ω => by simp⟩ (fun t => by simp)
  obtain ⟨p, _, hpu⟩ := hdet 0
  have hbu0 : 0 ≤ bu := (abs_nonneg _).trans (hbu 0 (Classical.arbitrary Ω))
  have e1 := hpu (y, dRec γ (fun t => c 0 • y t 0 + c 1 • y t 1 + (0 : ℕ → Ω → ℝ) t)
    (fun _ => 0)) ⟨⟨hy, rfl, fun t => rfl⟩, hay, hby, dRec_adapted 𝔼 hau,
      ⟨0 + bu / (1 - |γ|), rec_bounded hγ le_rfl hbu0 hbu (fun t => rfl)
        (fun ω => by simp [dRec])⟩⟩
  have e2 := hpu (0, 0) ⟨⟨hz, by funext ω; rfl, fun t => by funext ω; simp⟩,
    fun t i => by simp, ⟨0, fun t i ω => by simp⟩, fun t => by simp,
    ⟨0, fun t ω => by simp⟩⟩
  exact hne (congrArg Prod.fst (e1.trans e2.symm))

/-- **Proposition 4.11, Ricardian case** (Woodford (2003), App. C.8, pp. 685–686), abstract
form: if `|γ| < 1` the stacked system is determinate iff the `2 × 2` block `A` is (the debt
row never restricts `z`, and it inherits boundedness from `z`); the unique `z` is the forward
solution (2.34) (`BlanchardKahn.fwd_existsUnique`). -/
theorem determinate3_ricardian [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ}
    {γ : ℝ} (hγ : |γ| < 1) :
    Determinate3 𝔼 A c γ ↔ SchurStable (tr2 A) (det2 A) := by
  constructor
  · intro hdet
    by_contra hA
    exact not_zeroDet_ricardian 𝔼 hγ hA (zeroDet_of_determinate3 𝔼 hdet)
  · intro hA w f b0 hw haw hf haf
    obtain ⟨z, ⟨hz, haz, hbz⟩, hzu⟩ := fwd_existsUnique 𝔼 hA hw haw
    obtain ⟨⟨bu, hbu⟩, hau⟩ := coupling_bounded_adapted 𝔼 c hbz haz hf haf
    have hbu0 : 0 ≤ bu := (abs_nonneg _).trans (hbu 0 (Classical.arbitrary Ω))
    refine ⟨(z, dRec γ (fun t => c 0 • z t 0 + c 1 • z t 1 + f t) (fun _ => b0)),
      ⟨⟨hz, rfl, fun t => rfl⟩, haz, hbz, dRec_adapted 𝔼 hau,
        ⟨|b0| + bu / (1 - |γ|), rec_bounded hγ (abs_nonneg b0) hbu0 hbu (fun t => rfl)
          (fun ω => le_rfl)⟩⟩, fun q hq => ?_⟩
    obtain ⟨⟨hq1, hq2, hq3⟩, hq4, hq5, -, -⟩ := hq
    have hzq : q.1 = z := hzu q.1 ⟨hq1, hq4, hq5⟩
    have hdq := eq_dRec hq3
    rw [hq2, hzq] at hdq
    exact Prod.ext hzq hdq

/-- **Proposition 4.11, non-Ricardian case under the Taylor principle** (Woodford (2003),
p. 314, App. C.8): if `|γ| > 1` and `A` is Schur–Cohn stable, then for given disturbances at
most one initial debt `b̂_{−1}` admits a bounded equilibrium — so for all but one initial
condition there is none ("for almost all possible initial conditions", made precise). -/
theorem nonricardian_TP_initial {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ} {γ : ℝ}
    (hγ : 1 < |γ|) (hA : SchurStable (tr2 A) (det2 A)) [Nonempty Ω]
    (w : ℕ → Fin 2 → Ω → ℝ) (f : ℕ → Ω → ℝ) :
    {b0 : ℝ | ∃ z d, Eq3 𝔼 A c γ w f b0 z d ∧ 𝔼.AdaptedVec z ∧ BoundedVec z ∧
      BoundedProc d}.Subsingleton := by
  rintro b0 ⟨z, d, ⟨hz, hd0, hd⟩, haz, hbz, hbd⟩ b0' ⟨z', d', ⟨hz', hd0', hd'⟩, haz', hbz', hbd'⟩
  have hzz := 𝔼.system_unique hA hz hz' haz haz' hbz hbz'
  subst hzz
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨M', hM'⟩ := hbd'
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have key : ∀ t, d t ω - d' t ω = γ ^ t * (b0 - b0') := by
    intro t
    induction t with
    | zero => simp [hd0, hd0']
    | succ t ih =>
      rw [hd t, hd' t]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [pow_succ]
      linear_combination γ * ih
  have h0 := pow_bounded_eq_zero hγ (M := M + M') (fun t => by
    rw [← key t]; exact (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω)))
  linarith

/-- **Proposition 4.11, non-Ricardian case under the Taylor principle** (Woodford (2003),
p. 314): likewise, perturbing the date-0 fiscal disturbance by `ε` destroys existence for all but
one value of `ε` ("for almost all realizations of the exogenous disturbances"). -/
theorem nonricardian_TP_shock {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ} {γ : ℝ}
    (hγ : 1 < |γ|) (hA : SchurStable (tr2 A) (det2 A)) [Nonempty Ω]
    (w : ℕ → Fin 2 → Ω → ℝ) (f : ℕ → Ω → ℝ) (b0 : ℝ) :
    {ε : ℝ | ∃ z d, Eq3 𝔼 A c γ w (fun t => f t + fun _ => if t = 0 then ε else 0) b0 z d ∧
      𝔼.AdaptedVec z ∧ BoundedVec z ∧ BoundedProc d}.Subsingleton := by
  rintro ε ⟨z, d, ⟨hz, hd0, hd⟩, haz, hbz, hbd⟩ ε' ⟨z', d', ⟨hz', hd0', hd'⟩, haz', hbz', hbd'⟩
  have hzz := 𝔼.system_unique hA hz hz' haz haz' hbz hbz'
  subst hzz
  obtain ⟨M, hM⟩ := hbd
  obtain ⟨M', hM'⟩ := hbd'
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have key : ∀ t, d (t + 1) ω - d' (t + 1) ω = γ ^ t * (ε - ε') := by
    intro t
    induction t with
    | zero =>
      rw [hd 0, hd' 0, hd0, hd0']
      simp
    | succ t ih =>
      rw [hd (t + 1), hd' (t + 1)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_one_ne_zero, ↓reduceIte,
        add_zero]
      rw [pow_succ]
      linear_combination γ * ih
  have h0 := pow_bounded_eq_zero hγ (M := M + M') (fun t => by
    rw [← key t]; exact (abs_sub _ _).trans (add_le_add (hM (t + 1) ω) (hM' (t + 1) ω)))
  linarith

/-- **Proposition 4.11** (Woodford (2003), p. 314): with a non-Ricardian rule (`|γ| > 1`) and
the Taylor principle (`A` Schur–Cohn stable), even the undisturbed system is not determinate:
the initial debt `b̂_{−1} = 1` admits no bounded solution. -/
theorem not_zeroDet_nonricardian_TP [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ}
    {c : Fin 2 → ℝ} {γ : ℝ} (hγ : 1 < |γ|) (hA : SchurStable (tr2 A) (det2 A)) :
    ¬ ZeroDet 𝔼 A c γ := by
  intro hdet
  have ex : ∀ b0 : ℝ, b0 ∈ {b0 : ℝ | ∃ z d, Eq3 𝔼 A c γ 0 0 b0 z d ∧ 𝔼.AdaptedVec z ∧
      BoundedVec z ∧ BoundedProc d} := by
    intro b0
    obtain ⟨p, ⟨h1, h2, h3, -, h5⟩, -⟩ := hdet b0
    exact ⟨p.1, p.2, h1, h2, h3, h5⟩
  have := nonricardian_TP_initial 𝔼 hγ hA 0 0 (ex 0) (ex 1)
  norm_num at this

/-- **Proposition 4.11** (Woodford (2003), p. 314): a non-Ricardian rule (`|γ| > 1`) together
with the Taylor principle is never determinate (`not_zeroDet_nonricardian_TP`). -/
theorem not_determinate3_nonricardian_TP [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ}
    {c : Fin 2 → ℝ} {γ : ℝ} (hγ : 1 < |γ|) (hA : SchurStable (tr2 A) (det2 A)) :
    ¬ Determinate3 𝔼 A c γ := fun h =>
  not_zeroDet_nonricardian_TP 𝔼 hγ hA (zeroDet_of_determinate3 𝔼 h)

/-! ### Non-Ricardian policy without the Taylor principle: the exact non-degeneracy -/

/-- Woodford (2003), App. C.8, p. 685: `l·r = l₀r₀ + l₁r₁`. -/
def dot2 (l r : Fin 2 → ℝ) : ℝ := l 0 * r 0 + l 1 * r 1

/-- Woodford (2003), App. C.8, p. 685: a real spectral decomposition of the `2 × 2` block,
`A = λ₁ r₁ l₁ᵀ + λ₂ r₂ l₂ᵀ`, with biorthonormal left and right eigenvectors
(`l_i·r_j = δ_ij`, `r₁l₁ᵀ + r₂l₂ᵀ = I`). -/
def Spectral (A : Matrix (Fin 2) (Fin 2) ℝ) (l1 l2 r1 r2 : Fin 2 → ℝ) (lam1 lam2 : ℝ) : Prop :=
  (∀ i j, A i j = lam1 * r1 i * l1 j + lam2 * r2 i * l2 j) ∧ dot2 l1 r1 = 1 ∧ dot2 l1 r2 = 0 ∧
    dot2 l2 r1 = 0 ∧ dot2 l2 r2 = 1 ∧ ∀ i j, r1 i * l1 j + r2 i * l2 j = if i = j then 1 else 0

/-- Woodford (2003), App. C.8: the coordinate `l·z_t` of a vector process. -/
def proj (l : Fin 2 → ℝ) (z : ℕ → Fin 2 → Ω → ℝ) : ℕ → Ω → ℝ := fun t => l 0 • z t 0 + l 1 • z t 1

/-- Woodford (2003), App. C.8: a left eigenvector of `A` decouples the system:
`l·z_t = λ E_t(l·z_{t+1}) + l·w_t`. -/
theorem proj_solves {A : Matrix (Fin 2) (Fin 2) ℝ} {l : Fin 2 → ℝ} {lam : ℝ}
    (hl : ∀ k, l 0 * A 0 k + l 1 * A 1 k = lam * l k) {w z : ℕ → Fin 2 → Ω → ℝ}
    (hz : 𝔼.Solves A w z) (t : ℕ) :
    proj l z t = lam • 𝔼.E t (proj l z (t + 1)) + proj l w t := by
  funext ω
  have h0 := congrFun (hz t 0) ω
  have h1 := congrFun (hz t 1) ω
  simp only [proj, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul] at h0 h1 ⊢
  rw [h0, h1]
  linear_combination 𝔼.E t (z (t + 1) 0) ω * hl 0 + 𝔼.E t (z (t + 1) 1) ω * hl 1

/-- Woodford (2003), App. C.8: the left eigenvectors of a spectral decomposition. -/
theorem left_eigen {A : Matrix (Fin 2) (Fin 2) ℝ} {l1 l2 r1 r2 : Fin 2 → ℝ} {lam1 lam2 : ℝ}
    (hS : Spectral A l1 l2 r1 r2 lam1 lam2) :
    (∀ k, l1 0 * A 0 k + l1 1 * A 1 k = lam1 * l1 k) ∧
      (∀ k, l2 0 * A 0 k + l2 1 * A 1 k = lam2 * l2 k) := by
  obtain ⟨hA, d11, d12, d21, d22, -⟩ := hS
  unfold dot2 at d11 d12 d21 d22
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [hA 0 k, hA 1 k]
    linear_combination lam1 * l1 k * d11 + lam2 * l2 k * d12
  · rw [hA 0 k, hA 1 k]
    linear_combination lam1 * l1 k * d21 + lam2 * l2 k * d22

/-- Woodford (2003), App. C.8: reconstruction `z_j = r₁_j (l₁·z) + r₂_j (l₂·z)`. -/
theorem recon {A : Matrix (Fin 2) (Fin 2) ℝ} {l1 l2 r1 r2 : Fin 2 → ℝ} {lam1 lam2 : ℝ}
    (hS : Spectral A l1 l2 r1 r2 lam1 lam2) (z : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) (j : Fin 2) :
    z t j = r1 j • proj l1 z t + r2 j • proj l2 z t := by
  obtain ⟨-, -, -, -, -, hc⟩ := hS
  funext ω
  have c0 := hc j 0
  have c1 := hc j 1
  simp only [proj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases j
  · simp only [Fin.zero_eta, ↓reduceIte, Fin.isValue] at c0 c1
    simp only [Fin.zero_eta, Fin.isValue]
    norm_num at c1
    linear_combination (-(z t 0 ω)) * c0 - z t 1 ω * c1
  · simp only [Fin.mk_one, Fin.isValue] at c0 c1
    norm_num at c0 c1
    simp only [Fin.mk_one, Fin.isValue]
    linear_combination (-(z t 0 ω)) * c0 - z t 1 ω * c1

/-- Woodford (2003), App. C.8: conversely, if `y₁`, `y₂` solve the decoupled equations
`y_i,t = λ_i E_t y_i,t+1 + l_i·w_t`, then `z_t = r₁ y₁,t + r₂ y₂,t` solves the system. -/
theorem solves_of_proj {A : Matrix (Fin 2) (Fin 2) ℝ} {l1 l2 r1 r2 : Fin 2 → ℝ} {lam1 lam2 : ℝ}
    (hS : Spectral A l1 l2 r1 r2 lam1 lam2) {w : ℕ → Fin 2 → Ω → ℝ} {y1 y2 : ℕ → Ω → ℝ}
    (h1 : ∀ t, y1 t = lam1 • 𝔼.E t (y1 (t + 1)) + proj l1 w t)
    (h2 : ∀ t, y2 t = lam2 • 𝔼.E t (y2 (t + 1)) + proj l2 w t) :
    𝔼.Solves A w (fun t j => r1 j • y1 t + r2 j • y2 t) := by
  intro t j
  have hw := recon hS w t j
  obtain ⟨hA, d11, d12, d21, d22, -⟩ := hS
  unfold dot2 at d11 d12 d21 d22
  funext ω
  have e1 := congrFun (h1 t) ω
  have e2 := congrFun (h2 t) ω
  have ew := congrFun hw ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul] at e1 e2 ew ⊢
  rw [hA j 0, hA j 1]
  set Y1 := 𝔼.E t (y1 (t + 1)) ω
  set Y2 := 𝔼.E t (y2 (t + 1)) ω
  linear_combination r1 j * e1 + r2 j * e2 - ew - lam1 * r1 j * Y1 * d11 -
    lam1 * r1 j * Y2 * d12 - lam2 * r2 j * Y1 * d21 - lam2 * r2 j * Y2 * d22

/-- Woodford (2003), App. C.8: the coordinate of a bounded adapted vector process is bounded
and adapted. -/
theorem proj_bounded_adapted (l : Fin 2 → ℝ) {z : ℕ → Fin 2 → Ω → ℝ} (hz : BoundedVec z)
    (haz : 𝔼.AdaptedVec z) : BoundedProc (proj l z) ∧ 𝔼.Adapted (proj l z) := by
  obtain ⟨⟨K, hK⟩, ha⟩ := coupling_bounded_adapted 𝔼 l hz haz (f := 0) ⟨0, fun t ω => by simp⟩
    (fun t => by simp)
  refine ⟨⟨K, fun t ω => ?_⟩, fun t => ?_⟩
  · simpa [proj] using hK t ω
  · simpa [proj] using ha t

/-- **Proposition 4.11, non-Ricardian case, uniqueness** (Woodford (2003), App. C.8): with
`|γ| > 1`, a spectral decomposition with `|λ₁| < 1 < |λ₂|`, and the non-degeneracy
`κ₂ = c·r₂ ≠ 0` (the debt equation loads on the eigen-direction `r₂` that would otherwise carry
self-fulfilling fluctuations), two bounded adapted solutions of the stacked system with the same
data coincide. The proof: the stable coordinate is pinned by forward iteration; the debt
recursion, solved forward with `|γ⁻¹| < 1`, forces `d_t + κ₂(γ − λ₂⁻¹)⁻¹ y₂,t = 0`, and the
initial debt then pins `y₂ = 0`. -/
theorem unique3_spectral {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ} {γ : ℝ}
    {l1 l2 r1 r2 : Fin 2 → ℝ} {lam1 lam2 : ℝ} (hγ : 1 < |γ|)
    (hS : Spectral A l1 l2 r1 r2 lam1 lam2) (h1 : |lam1| < 1) (h2 : 1 < |lam2|)
    (hk : dot2 c r2 ≠ 0) {w : ℕ → Fin 2 → Ω → ℝ} {f : ℕ → Ω → ℝ} {b0 : ℝ}
    {z z' : ℕ → Fin 2 → Ω → ℝ} {d d' : ℕ → Ω → ℝ}
    (he : Eq3 𝔼 A c γ w f b0 z d) (he' : Eq3 𝔼 A c γ w f b0 z' d')
    (haz : 𝔼.AdaptedVec z) (hbz : BoundedVec z) (had : 𝔼.Adapted d) (hbd : BoundedProc d)
    (haz' : 𝔼.AdaptedVec z') (hbz' : BoundedVec z') (had' : 𝔼.Adapted d')
    (hbd' : BoundedProc d') : z = z' ∧ d = d' := by
  obtain ⟨hz, hd0, hd⟩ := he
  obtain ⟨hz', hd0', hd'⟩ := he'
  obtain ⟨hl1, hl2⟩ := left_eigen hS
  set δ : ℕ → Fin 2 → Ω → ℝ := fun t i => z t i - z' t i with hδ
  have hsol : 𝔼.Solves A 0 δ := by
    intro t i
    simp only [hδ, map_sub, smul_sub, Pi.zero_apply, add_zero]
    rw [hz t i, hz' t i]
    abel
  have haδ : 𝔼.AdaptedVec δ := fun t i => by simp only [hδ, map_sub, haz t i, haz' t i]
  have hbδ : BoundedVec δ := by
    obtain ⟨M, hM⟩ := hbz
    obtain ⟨M', hM'⟩ := hbz'
    exact ⟨M + M', fun t i ω => (abs_sub _ _).trans (add_le_add (hM t i ω) (hM' t i ω))⟩
  obtain ⟨hby1, hay1⟩ := proj_bounded_adapted 𝔼 l1 hbδ haδ
  obtain ⟨hby2, hay2⟩ := proj_bounded_adapted 𝔼 l2 hbδ haδ
  have hp0 : ∀ l t, proj l (0 : ℕ → Fin 2 → Ω → ℝ) t = 0 := fun l t => by
    funext ω; simp [proj]
  have hy1 : ∀ t, proj l1 δ t = lam1 • 𝔼.E t (proj l1 δ (t + 1)) + (0 : ℕ → Ω → ℝ) t := by
    intro t; rw [proj_solves 𝔼 hl1 hsol t, hp0]; rfl
  have hy10 : proj l1 δ = 0 := 𝔼.forward_unique h1 hy1 (fun t => by simp)
    hby1 ⟨0, fun t ω => by simp⟩
  have hy2 : ∀ t, proj l2 δ t = lam2 • 𝔼.E t (proj l2 δ (t + 1)) := by
    intro t; rw [proj_solves 𝔼 hl2 hsol t, hp0, add_zero]
  have hδr : ∀ t j, δ t j = r2 j • proj l2 δ t := by
    intro t j
    rw [recon hS δ t j, hy10]
    simp
  set κ2 := dot2 c r2 with hκ2
  set e : ℕ → Ω → ℝ := fun t => d t - d' t with he_def
  have herec : ∀ t, e (t + 1) = γ • e t + κ2 • proj l2 δ t := by
    intro t
    simp only [he_def]
    rw [hd t, hd' t]
    funext ω
    have a0 := congrFun (hδr t 0) ω
    have a1 := congrFun (hδr t 1) ω
    simp only [hδ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at a0 a1
    simp only [hκ2, dot2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination c 0 * a0 + c 1 * a1
  have hae : 𝔼.Adapted e := fun t => by simp only [he_def, map_sub, had t, had' t]
  have hbe : BoundedProc e := by
    obtain ⟨M, hM⟩ := hbd
    obtain ⟨M', hM'⟩ := hbd'
    exact ⟨M + M', fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))⟩
  have hγ0 : γ ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  have hl0 : lam2 ≠ 0 := fun h => by rw [h, abs_zero] at h2; linarith
  have hli : |lam2⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ h2
  have hgl : γ - lam2⁻¹ ≠ 0 := by
    intro h
    have : γ = lam2⁻¹ := by linarith
    rw [this] at hγ; linarith
  have hEy2 : ∀ t, 𝔼.E t (proj l2 δ (t + 1)) = lam2⁻¹ • proj l2 δ t := by
    intro t
    rw [hy2 t, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  set q := κ2 / (γ - lam2⁻¹) with hq
  set ψ : ℕ → Ω → ℝ := fun t => e t + q • proj l2 δ t with hψ
  have hψeq : ∀ t, ψ t = γ⁻¹ • 𝔼.E t (ψ (t + 1)) + (0 : ℕ → Ω → ℝ) t := by
    intro t
    simp only [hψ, map_add, map_smul, herec t, hEy2 t, hae t, hay2 t, Pi.zero_apply,
      add_zero]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hm : γ * lam2 - 1 ≠ 0 := by
      intro h
      apply hgl
      field_simp
      linarith
    rw [hq]
    field_simp
    ring
  have hγi : |γ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hγ
  have hψ0 : ψ = 0 := by
    obtain ⟨Me, hMe⟩ := hbe
    obtain ⟨My, hMy⟩ := hby2
    refine 𝔼.forward_unique hγi hψeq (fun t => by simp) ⟨Me + |q| * My, fun t ω => ?_⟩
      ⟨0, fun t ω => by simp⟩
    simp only [hψ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hMe t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMy t ω) (abs_nonneg q)
  have hqne : q ≠ 0 := div_ne_zero hk hgl
  have hy2e : ∀ t, proj l2 δ t = -q⁻¹ • e t := by
    intro t
    have := congrFun hψ0 t
    simp only [hψ, Pi.zero_apply] at this
    funext ω
    have h := congrFun this ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, neg_mul] at h ⊢
    field_simp
    linarith
  have he0 : ∀ t, e t = 0 := by
    intro t
    induction t with
    | zero => simp only [he_def, hd0, hd0', sub_self]
    | succ t ih => rw [herec t, hy2e t, ih]; simp
  have hy20 : proj l2 δ = 0 := by
    funext t
    rw [hy2e t, he0 t, smul_zero]
    rfl
  refine ⟨?_, ?_⟩
  · funext t j ω
    have := congrFun (hδr t j) ω
    rw [hy20] at this
    simp only [hδ, Pi.zero_apply, Pi.sub_apply, smul_zero] at this
    linarith
  · funext t ω
    have := congrFun (he0 t) ω
    simp only [he_def, Pi.sub_apply, Pi.zero_apply] at this
    linarith

/-- **Proposition 4.11, non-Ricardian case, existence** (Woodford (2003), App. C.8): under the
hypotheses of `unique3_spectral` a bounded adapted solution exists for all bounded adapted
disturbances and every initial debt. Construction: the stable coordinate is the forward series;
the unstable coordinate is a particular bounded solution plus the self-fulfilling component
`h_{t+1} = λ₂⁻¹ h_t + ν_{t+1}`, whose initial value and martingale-difference innovations are
chosen (possible because `κ₂ ≠ 0`) to keep debt `d_t = β_t + θ h_t` bounded, where `β` is the
forward solution of the debt equation and `θ = κ₂/(λ₂⁻¹ − γ)`. -/
theorem exists3_spectral {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ} {γ : ℝ}
    {l1 l2 r1 r2 : Fin 2 → ℝ} {lam1 lam2 : ℝ} (hγ : 1 < |γ|)
    (hS : Spectral A l1 l2 r1 r2 lam1 lam2) (h1 : |lam1| < 1) (h2 : 1 < |lam2|)
    (hk : dot2 c r2 ≠ 0) {w : ℕ → Fin 2 → Ω → ℝ} {f : ℕ → Ω → ℝ} (b0 : ℝ)
    (hw : BoundedVec w) (haw : 𝔼.AdaptedVec w) (hf : BoundedProc f) (haf : 𝔼.Adapted f) :
    ∃ z d, Eq3 𝔼 A c γ w f b0 z d ∧ 𝔼.AdaptedVec z ∧ BoundedVec z ∧ 𝔼.Adapted d ∧
      BoundedProc d := by
  have hγ0 : γ ≠ 0 := fun h => by rw [h, abs_zero] at hγ; linarith
  have hl0 : lam2 ≠ 0 := fun h => by rw [h, abs_zero] at h2; linarith
  have hgl : lam2⁻¹ - γ ≠ 0 := by
    intro h
    have hli : |lam2⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ h2
    have : lam2⁻¹ = γ := by linarith
    rw [this] at hli; linarith
  have hγi : |γ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hγ
  obtain ⟨⟨B1, hu1b⟩, hu1a⟩ := proj_bounded_adapted 𝔼 l1 hw haw
  obtain ⟨⟨B2, hu2b⟩, hu2a⟩ := proj_bounded_adapted 𝔼 l2 hw haw
  obtain ⟨Bf, hBf⟩ := hf
  -- the stable coordinate
  set y1 := 𝔼.forwardSeries lam1 (proj l1 w) with hy1
  have hy1s : ∀ t, y1 t = lam1 • 𝔼.E t (y1 (t + 1)) + proj l1 w t :=
    ForwardSolution.forwardSeries_solves_abs 𝔼 h1 hu1b hu1a
  obtain ⟨By1, hy1b⟩ : BoundedProc y1 := ForwardSolution.forwardSeries_bounded_abs 𝔼 h1 hu1b
  have hy1a : 𝔼.Adapted y1 := ForwardSolution.forwardSeries_adapted_abs 𝔼 h1 hu1b
  -- a particular bounded solution for the unstable coordinate
  set p := ForwardSolution.sunspotFamily lam2 (proj l2 w) 0 0 with hp
  have hps : ∀ t, p t = lam2 • 𝔼.E t (p (t + 1)) + proj l2 w t :=
    ForwardSolution.sunspotFamily_solves 𝔼 hl0 (z0 := 0) (ν := 0) (by simp) hu2a
      (fun t => by simp) (fun t => by simp)
  obtain ⟨Bp, hpb⟩ : BoundedProc p := ForwardSolution.sunspotFamily_bounded (B := 0) (Mν := 0)
    h2 (z0 := 0) (ν := 0) (fun ω => by simp) hu2b (fun t ω => by simp)
  have hpa : 𝔼.Adapted p := ForwardSolution.sunspotFamily_adapted 𝔼 (a := lam2) (z0 := 0)
    (ν := 0) (by simp) hu2a (fun t => by simp)
  -- the forward solution of the debt equation
  set κ1 := dot2 c r1 with hκ1
  set κ2 := dot2 c r2 with hκ2
  set g : ℕ → Ω → ℝ := fun t => κ1 • y1 t + κ2 • p t + f t with hg
  set G : ℕ → Ω → ℝ := fun t => -γ⁻¹ • g t with hG
  have hGb : ∀ t ω, |G t ω| ≤ |γ⁻¹| * (|κ1| * By1 + |κ2| * Bp + Bf) := by
    intro t ω
    simp only [hG, hg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, abs_neg, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) (hBf t ω))
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hy1b t ω) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hpb t ω) (abs_nonneg _))
  have hGa : 𝔼.Adapted G := fun t => by
    simp only [hG, hg, map_smul, map_add, hy1a t, hpa t, haf t]
  set bt := 𝔼.forwardSeries γ⁻¹ G with hbt
  have hbs : ∀ t, bt t = γ⁻¹ • 𝔼.E t (bt (t + 1)) + G t :=
    ForwardSolution.forwardSeries_solves_abs 𝔼 hγi hGb hGa
  obtain ⟨Bb, hbb⟩ : BoundedProc bt := ForwardSolution.forwardSeries_bounded_abs 𝔼 hγi hGb
  have hba : 𝔼.Adapted bt := ForwardSolution.forwardSeries_adapted_abs 𝔼 hγi hGb
  -- the self-fulfilling component, tuned to the debt equation
  set θ := κ2 / (lam2⁻¹ - γ) with hθ
  have hθ0 : θ ≠ 0 := div_ne_zero hk hgl
  have hθk : θ * (lam2⁻¹ - γ) = κ2 := by rw [hθ, div_mul_cancel₀ _ hgl]
  set ν : ℕ → Ω → ℝ := fun t => -θ⁻¹ • (bt t - 𝔼.E (t - 1) (bt t)) with hν
  have hνa : 𝔼.Adapted ν := by
    intro t
    simp only [hν, map_smul, map_sub, hba t,
      ForwardSolution.E_of_known 𝔼 (Nat.sub_le t 1) (𝔼.E_E_self (t - 1) (bt t))]
  have hνmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0 := by
    intro t
    simp only [hν, map_smul, map_sub, Nat.add_sub_cancel, 𝔼.E_E_self, sub_self, smul_zero]
  have hνb : ∀ t ω, |ν t ω| ≤ |θ⁻¹| * (Bb + Bb) := by
    intro t ω
    simp only [hν, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, neg_mul, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hbb t ω)
      (𝔼.abs_E_le (hbb t) (t - 1) ω))) (abs_nonneg _)
  set h0 : Ω → ℝ := θ⁻¹ • ((fun _ => b0) - bt 0) with hh0
  have hh0a : 𝔼.E 0 h0 = h0 := by simp only [hh0, map_smul, map_sub, 𝔼.const, hba 0]
  set h := ForwardSolution.sunspotFamily lam2 0 ν h0 with hh
  have hhs : ∀ t, h t = lam2 • 𝔼.E t (h (t + 1)) + (0 : ℕ → Ω → ℝ) t :=
    ForwardSolution.sunspotFamily_solves 𝔼 hl0 (u := 0) hh0a (fun t => by simp) hνa hνmd
  obtain ⟨Bh, hhb⟩ : BoundedProc h := ForwardSolution.sunspotFamily_bounded (u := 0) (Mu := 0)
    (B := |θ⁻¹| * (|b0| + Bb)) h2 (z0 := h0) (fun ω => by
      simp only [hh0, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add le_rfl (hbb 0 ω)))
        (abs_nonneg _)) (fun t ω => by simp) hνb
  have hha : 𝔼.Adapted h := ForwardSolution.sunspotFamily_adapted 𝔼 (a := lam2) (u := 0) hh0a
    (fun t => by simp) hνa
  -- the unstable coordinate and the state
  set y2 : ℕ → Ω → ℝ := fun t => p t + h t with hy2
  have hy2s : ∀ t, y2 t = lam2 • 𝔼.E t (y2 (t + 1)) + proj l2 w t := by
    intro t
    simp only [hy2, map_add, smul_add]
    rw [hps t, hhs t]
    simp only [Pi.zero_apply, add_zero]
    abel
  refine ⟨fun t j => r1 j • y1 t + r2 j • y2 t, fun t => bt t + θ • h t,
    ⟨solves_of_proj 𝔼 hS hy1s hy2s, ?_, fun t => ?_⟩, fun t j => ?_, ⟨|r1 0| * By1 +
      |r1 1| * By1 + (|r2 0| + |r2 1|) * (Bp + Bh), fun t j ω => ?_⟩, fun t => ?_,
      ⟨Bb + |θ| * Bh, fun t ω => ?_⟩⟩
  · funext ω
    change bt 0 ω + θ * (θ⁻¹ * (b0 - bt 0 ω)) = b0
    field_simp
    ring
  · funext ω
    have eh : h (t + 1) ω = lam2⁻¹ * h t ω + ν (t + 1) ω := by
      rw [hh, ForwardSolution.sunspotFamily_succ]
      simp
    have eν : ν (t + 1) ω = -θ⁻¹ * (bt (t + 1) ω - 𝔼.E t (bt (t + 1)) ω) := by
      simp [hν]
    have eb := congrFun (hbs t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hG, hg, neg_mul] at eb
    have hE : 𝔼.E t (bt (t + 1)) ω = γ * bt t ω + (κ1 * y1 t ω + κ2 * p t ω + f t ω) := by
      rw [eb]
      field_simp
      ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy2]
    rw [eh, eν, hE]
    have hθi : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ0
    simp only [hκ1, hκ2, dot2] at hθk ⊢
    linear_combination (-(bt (t + 1) ω - (γ * bt t ω + ((c 0 * r1 0 + c 1 * r1 1) * y1 t ω +
      (c 0 * r2 0 + c 1 * r2 1) * p t ω + f t ω)))) * hθi + h t ω * hθk
  · simp only [map_add, map_smul, hy1a t, hy2, hpa t, hha t]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hy2]
    have a1 := hy1b t ω
    have a2 := hpb t ω
    have a3 := hhb t ω
    have e1 : |r1 j * y1 t ω| ≤ |r1 0| * By1 + |r1 1| * By1 := by
      rw [abs_mul]
      have hB : 0 ≤ By1 := (abs_nonneg _).trans a1
      fin_cases j
      · simp only [Fin.zero_eta]
        nlinarith [mul_le_mul_of_nonneg_left a1 (abs_nonneg (r1 0)), abs_nonneg (r1 1)]
      · simp only [Fin.mk_one]
        nlinarith [mul_le_mul_of_nonneg_left a1 (abs_nonneg (r1 1)), abs_nonneg (r1 0)]
    have e2 : |r2 j * (p t ω + h t ω)| ≤ (|r2 0| + |r2 1|) * (Bp + Bh) := by
      rw [abs_mul]
      have hB : |p t ω + h t ω| ≤ Bp + Bh := (abs_add_le _ _).trans (add_le_add a2 a3)
      have hB0 : 0 ≤ Bp + Bh := (abs_nonneg _).trans hB
      fin_cases j
      · simp only [Fin.zero_eta]
        nlinarith [mul_le_mul_of_nonneg_left hB (abs_nonneg (r2 0)), abs_nonneg (r2 1)]
      · simp only [Fin.mk_one]
        nlinarith [mul_le_mul_of_nonneg_left hB (abs_nonneg (r2 1)), abs_nonneg (r2 0)]
    exact (abs_add_le _ _).trans (add_le_add e1 e2)
  · simp only [map_add, map_smul, hba t, hha t]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hbb t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hhb t ω) (abs_nonneg _)

/-- **Proposition 4.11, non-Ricardian case without the Taylor principle** (Woodford (2003),
App. C.8): under the exact non-degeneracy `c·r₂ ≠ 0` the stacked system is determinate. -/
theorem determinate3_spectral {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ} {γ : ℝ}
    {l1 l2 r1 r2 : Fin 2 → ℝ} {lam1 lam2 : ℝ} (hγ : 1 < |γ|)
    (hS : Spectral A l1 l2 r1 r2 lam1 lam2) (h1 : |lam1| < 1) (h2 : 1 < |lam2|)
    (hk : dot2 c r2 ≠ 0) : Determinate3 𝔼 A c γ := by
  intro w f b0 hw haw hf haf
  obtain ⟨z, d, he, haz, hbz, had, hbd⟩ := exists3_spectral 𝔼 hγ hS h1 h2 hk b0 hw haw hf haf
  refine ⟨(z, d), ⟨he, haz, hbz, had, hbd⟩, fun q ⟨hq, hq1, hq2, hq3, hq4⟩ => ?_⟩
  obtain ⟨e1, e2⟩ := unique3_spectral 𝔼 hγ hS h1 h2 hk hq he hq1 hq2 hq3 hq4 haz hbz had hbd
  exact Prod.ext e1 e2

/-- **Proposition 4.11: the non-degeneracy is needed** (Woodford (2003), App. C.8): if the debt
equation does not load on an eigen-direction `r ≠ 0` of `A` with eigenvalue `|λ| ≥ 1`
(`c·r = 0`), already the undisturbed stacked system is not determinate, whatever `γ`: next to
the zero solution there is the bounded solution `z_t = λ^{−t} r` with unchanged debt. -/
theorem not_zeroDet_degenerate [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ}
    {c : Fin 2 → ℝ} {γ : ℝ} {r : Fin 2 → ℝ} {lam : ℝ} (hr : r ≠ 0) (hlam : 1 ≤ |lam|)
    (hAr : ∀ i, A i 0 * r 0 + A i 1 * r 1 = lam * r i) (hc : dot2 c r = 0) :
    ¬ ZeroDet 𝔼 A c γ := by
  intro hdet
  have hl0 : lam ≠ 0 := fun h => by rw [h, abs_zero] at hlam; linarith
  set z : ℕ → Fin 2 → Ω → ℝ := fun t i _ => lam⁻¹ ^ t * r i with hz
  obtain ⟨p, _, hpu⟩ := hdet 0
  have hzs : 𝔼.Solves A 0 z := by
    intro t i
    funext ω
    simp only [hz, 𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      add_zero]
    have := hAr i
    calc lam⁻¹ ^ t * r i = lam⁻¹ ^ (t + 1) * (lam * r i) := by
          rw [pow_succ]; field_simp
      _ = _ := by rw [← this]; ring
  have hlb : ∀ t : ℕ, |lam⁻¹ ^ t| ≤ 1 := fun t => by
    rw [abs_pow, abs_inv]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hlam)
  have e1 := hpu (z, 0) ⟨⟨hzs, by funext ω; rfl, fun t => by
      funext ω
      simp only [hz, Pi.zero_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero,
        zero_add, add_zero]
      unfold dot2 at hc
      linear_combination (-(lam⁻¹ ^ t)) * hc⟩,
    fun t i => by simp [hz, 𝔼.const], ⟨|r 0| + |r 1|, fun t i ω => by
      simp only [hz, abs_mul]
      have := hlb t
      fin_cases i
      · simp only [Fin.zero_eta]; nlinarith [abs_nonneg (r 0), abs_nonneg (r 1)]
      · simp only [Fin.mk_one]; nlinarith [abs_nonneg (r 0), abs_nonneg (r 1)]⟩,
    fun t => by simp, ⟨0, fun t ω => by simp⟩⟩
  have e2 := hpu (0, 0) ⟨⟨fun t i => by simp, by funext ω; rfl, fun t => by funext ω; simp⟩,
    fun t i => by simp, ⟨0, fun t i ω => by simp⟩, fun t => by simp, ⟨0, fun t ω => by simp⟩⟩
  have hz0 := congrArg Prod.fst (e1.trans e2.symm)
  apply hr
  funext i
  have := congrFun (congrFun (congrFun hz0 0) i) (Classical.arbitrary Ω)
  simpa [hz] using this

/-- **Proposition 4.11: the non-degeneracy is needed** (Woodford (2003), App. C.8), for the
disturbed system (`not_zeroDet_degenerate`). -/
theorem not_determinate3_degenerate [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ}
    {c : Fin 2 → ℝ} {γ : ℝ} {r : Fin 2 → ℝ} {lam : ℝ} (hr : r ≠ 0) (hlam : 1 ≤ |lam|)
    (hAr : ∀ i, A i 0 * r 0 + A i 1 * r 1 = lam * r i) (hc : dot2 c r = 0) :
    ¬ Determinate3 𝔼 A c γ := fun h =>
  not_zeroDet_degenerate 𝔼 hr hlam hAr hc (zeroDet_of_determinate3 𝔼 h)

/-! ### The stacked matrix (survey error E29) -/

/-- Woodford (2003), App. C.8, p. 685: the stacked matrix `[[A, 0], [c, γ]]` of the system
`(E_t z_{t+1}, b̂_t) = M (z_t, b̂_{t−1}) + …`. -/
def stacked (A : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) (γ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; c 0, c 1, γ]

/-- Woodford (2003), App. C.8, p. 685 (**E29**): the characteristic polynomial of the stacked
matrix factors as `charpoly(A)(μ) · (μ − γ)` for every coupling `c`, so its eigenvalues are those
of `A` and `γ = β⁻¹(1 − τ_b)` as the book says. -/
theorem stacked_charpoly (A : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) (γ μ : ℝ) :
    (μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) - stacked A c γ).det =
      ((μ - A 0 0) * (μ - A 1 1) - A 0 1 * A 1 0) * (μ - γ) := by
  rw [Matrix.det_fin_three]
  simp [stacked]
  ring

/-- Woodford (2003), App. C.8, p. 685 (**E29**): the stacked matrix is block-diagonal — its
off-diagonal block `c` vanishes — only when the debt equation does not involve `z` at all; it is
block lower-triangular, not "block-diagonal" as printed. -/
theorem stacked_blockDiagonal_iff (A : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) (γ : ℝ) :
    (stacked A c γ 2 0 = 0 ∧ stacked A c γ 2 1 = 0) ↔ c = 0 := by
  simp only [stacked, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two]
  constructor
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · rintro rfl
    simp

/-! ### Real spectral decompositions of `2 × 2` matrices -/

/-- Woodford (2003), App. C.8: the left eigenvector `(λ − a₁₁, a₀₁)` for an eigenvalue `λ`. -/
def lvec (A : Matrix (Fin 2) (Fin 2) ℝ) (lam : ℝ) : Fin 2 → ℝ := ![lam - A 1 1, A 0 1]

/-- Woodford (2003), App. C.8: the right eigenvector `(a₀₁, λ − a₀₀)` for `λ`, normalised by
`a₀₁(λ − λ')` so that it is dual to `lvec` (`λ'` the other eigenvalue). -/
noncomputable def rvec (A : Matrix (Fin 2) (Fin 2) ℝ) (lam lam' : ℝ) : Fin 2 → ℝ :=
  ![A 0 1 / (A 0 1 * (lam - lam')), (lam - A 0 0) / (A 0 1 * (lam - lam'))]

/-- Woodford (2003), App. C.8: a real `2 × 2` matrix with `a₀₁ ≠ 0` and two distinct real roots
`λ₁ ≠ λ₂` of its characteristic polynomial (`λ₁ + λ₂ = tr A`, `λ₁λ₂ = det A`) has the spectral
decomposition `A = λ₁ r₁ l₁ᵀ + λ₂ r₂ l₂ᵀ` with `l_i = lvec`, `r_i = rvec`. -/
theorem spectral_of_roots {A : Matrix (Fin 2) (Fin 2) ℝ} {lam1 lam2 : ℝ}
    (hsum : lam1 + lam2 = tr2 A) (hprod : lam1 * lam2 = det2 A) (hne : lam1 ≠ lam2)
    (hb : A 0 1 ≠ 0) :
    Spectral A (lvec A lam1) (lvec A lam2) (rvec A lam1 lam2) (rvec A lam2 lam1) lam1 lam2 := by
  have h12 : lam1 - lam2 ≠ 0 := sub_ne_zero.mpr hne
  have h21 : lam2 - lam1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hA11 : A 1 1 = lam1 + lam2 - A 0 0 := by rw [hsum, tr2]; ring
  have hA10 : A 1 0 = (A 0 0 * (lam1 + lam2 - A 0 0) - lam1 * lam2) / A 0 1 := by
    rw [hprod, det2, ← hA11]; field_simp; ring
  refine ⟨fun i j => ?_, ?_, ?_, ?_, ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j <;>
      simp [lvec, rvec, hA10, hA11] <;> field_simp <;> ring
  · simp only [dot2, lvec, rvec, Matrix.cons_val_zero, Matrix.cons_val_one, hA11]
    field_simp; ring
  · simp only [dot2, lvec, rvec, Matrix.cons_val_zero, Matrix.cons_val_one, hA11]
    field_simp; ring
  · simp only [dot2, lvec, rvec, Matrix.cons_val_zero, Matrix.cons_val_one, hA11]
    field_simp; ring
  · simp only [dot2, lvec, rvec, Matrix.cons_val_zero, Matrix.cons_val_one, hA11]
    field_simp; ring
  · fin_cases i <;> fin_cases j <;> simp [lvec, rvec, hA11] <;> field_simp <;> ring

/-- Woodford (2003), App. C.8: `rvec` is an eigenvector, `A r = λ r`. -/
theorem rvec_eigen {A : Matrix (Fin 2) (Fin 2) ℝ} {lam1 lam2 : ℝ}
    (hsum : lam1 + lam2 = tr2 A) (hprod : lam1 * lam2 = det2 A) (hne : lam1 ≠ lam2)
    (hb : A 0 1 ≠ 0) (i : Fin 2) :
    A i 0 * rvec A lam2 lam1 0 + A i 1 * rvec A lam2 lam1 1 = lam2 * rvec A lam2 lam1 i := by
  have h21 : lam2 - lam1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hA11 : A 1 1 = lam1 + lam2 - A 0 0 := by rw [hsum, tr2]; ring
  have hA10 : A 1 0 = (A 0 0 * (lam1 + lam2 - A 0 0) - lam1 * lam2) / A 0 1 := by
    rw [hprod, det2, ← hA11]; field_simp; ring
  fin_cases i <;> simp [rvec, hA10, hA11] <;> field_simp <;> ring

/-! ### Proposition 4.11 for the basic model -/

/-- Woodford (2003), App. C.2, p. 677: the larger root `(T + √(T² − 4D))/2` of
`λ² − Tλ + D`. -/
noncomputable def lamPlus (T D : ℝ) : ℝ := (T + Real.sqrt (T ^ 2 - 4 * D)) / 2

/-- Woodford (2003), App. C.2, p. 677: the smaller root `(T − √(T² − 4D))/2`. -/
noncomputable def lamMinus (T D : ℝ) : ℝ := (T - Real.sqrt (T ^ 2 - 4 * D)) / 2

/-- Woodford (2003), App. C.2, p. 677 and §2.2, p. 253: when the Taylor principle is violated
strictly, the forward matrix `B` (`taylorB`) has real eigenvalues `0 < λ₁ < 1 < λ₂` (one root of the
book's matrix inside the unit circle, one outside). -/
theorem taylorB_roots {σ κ β φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hrev : φπ + (1 - β) * φx / (4 * κ) < 1) :
    let T := tr2 (taylorB β σ κ φπ φx)
    let D := det2 (taylorB β σ κ φπ φx)
    lamMinus T D + lamPlus T D = T ∧ lamMinus T D * lamPlus T D = D ∧ 0 < lamMinus T D ∧
      lamMinus T D < 1 ∧ 1 < lamPlus T D := by
  intro T D
  have hΔpos : 0 < taylorDelta σ κ φπ φx := taylorDelta_pos hσ hκ hφπ hφx
  have hD : D = β / taylorDelta σ κ φπ φx := taylorB_det hΔpos.ne'
  have hT : T = (1 + β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx :=
    taylorB_tr β σ κ φπ φx
  have hD0 : 0 < D := by rw [hD]; positivity
  have h1 : 1 + D - T < 0 := by
    have e1 : 1 + β / taylorDelta σ κ φπ φx - (1 + β + σ * κ + β * σ * φx / 4) /
        taylorDelta σ κ φπ φx =
          (κ * σ) * (φπ + (1 - β) * φx / (4 * κ) - 1) / taylorDelta σ κ φπ φx := by
      unfold taylorDelta
      field_simp
      ring
    rw [hD, hT, e1]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hκ hσ) (by linarith)) hΔpos
  have hdisc : 0 < T ^ 2 - 4 * D := by
    have a : 0 < T - (1 + D) := by linarith
    have b : 0 < T + (1 + D) := by linarith
    nlinarith [mul_pos a b, sq_nonneg (1 - D)]
  set s := Real.sqrt (T ^ 2 - 4 * D) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hdisc
  have hs2 : s ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hdisc.le
  have hsum : lamMinus T D + lamPlus T D = T := by unfold lamMinus lamPlus; ring
  have hprod : lamMinus T D * lamPlus T D = D := by
    unfold lamMinus lamPlus; rw [← hs]; nlinarith
  have hlt : lamMinus T D < lamPlus T D := by unfold lamMinus lamPlus; rw [← hs]; linarith
  have hq : (1 - lamMinus T D) * (1 - lamPlus T D) < 0 := by nlinarith
  have hm1 : lamMinus T D < 1 := by
    by_contra h
    push Not at h
    nlinarith
  have hp1 : 1 < lamPlus T D := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨hsum, hprod, ?_, hm1, hp1⟩
  by_contra h
  push Not at h
  nlinarith

/-- Woodford (2003), (4.5) with (1.14) and `Ŷ = x + Ŷⁿ`, p. 313: the coefficients of
`(π_t − π̄, x_t − x̄)` in the debt equation,
`c = (−β⁻¹(b̄ + τ_π) + (b̄ − β⁻¹τ_i)φ_π, −β⁻¹τ_y + (b̄ − β⁻¹τ_i)φ_x/4)`. -/
noncomputable def cvec411 (β bb τπ τy τi φπ φx : ℝ) : Fin 2 → ℝ :=
  ![-β⁻¹ * (bb + τπ) + (bb - β⁻¹ * τi) * φπ, -β⁻¹ * τy + (bb - β⁻¹ * τi) * (φx / 4)]

/-- Woodford (2003), (4.5), p. 313: the exogenous part of the debt equation once (1.14) and
`Ŷ = x + Ŷⁿ` are substituted. -/
noncomputable def f411 (β bb τg τπ τy τi πb xb : ℝ) (ib G v Yn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => β⁻¹ • (-(bb + τπ) • (fun _ => πb) + (1 - τg) • G t - τy • ((fun _ => xb) + Yn t)) +
    (bb - β⁻¹ * τi) • ib t - β⁻¹ • v t

/-- Woodford (2003), §4, pp. 311–314: the basic model (1.12)–(1.14) with the debt law (4.5)
(equivalently (4.2) with the tax rule (4.4), `debt42_iff_45`), output `Ŷ = x + Ŷⁿ`, the
nominal rate given by (1.14), and initial debt `b̂_{−1} = b₀` (`d_t = b̂_{t−1}`). -/
def Eq411 (σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ) (rn ib G v Yn : ℕ → Ω → ℝ) (b0 : ℝ)
    (π x d : ℕ → Ω → ℝ) : Prop :=
  TaylorEqm 𝔼 β σ κ φπ φx πb rn ib π x ∧ d 0 = (fun _ => b0) ∧
    Debt45 β bb τb τg τπ τy τi d π G (fun t => x t + Yn t)
      (taylorRate β κ φπ φx πb ib π x) v

/-- Woodford (2003), App. C.8, p. 685: the model of §4 is the stacked system with
`A = taylorB`, coupling `cvec411`, `γ = β⁻¹(1 − τ_b)`, forcing `fwdForcing taylorb` and `f411`
(`κ ≠ 0`, `Δ ≠ 0`). -/
theorem eq411_iff {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ} (hκ : κ ≠ 0)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {rn ib G v Yn : ℕ → Ω → ℝ} {b0 : ℝ} {π x d : ℕ → Ω → ℝ} :
    Eq411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi rn ib G v Yn b0 π x d ↔
      Eq3 𝔼 (taylorB β σ κ φπ φx) (cvec411 β bb τπ τy τi φπ φx) (β⁻¹ * (1 - τb))
        (fwdForcing (taylorb σ κ φπ φx) rn ib πb)
        (f411 β bb τg τπ τy τi πb (xbar β κ πb) ib G v Yn) b0
        (devStack π x πb (xbar β κ πb)) d := by
  unfold Eq411 Eq3 Debt45
  refine and_congr (taylorEqm_iff_solves 𝔼 hκ hΔ πb rn ib π x)
    (and_congr Iff.rfl (forall_congr' fun t => ?_))
  have key : β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t -
      τy • (fun t => x t + Yn t) t) + (bb - β⁻¹ * τi) •
        taylorRate β κ φπ φx πb ib π x t - β⁻¹ • v t =
      (β⁻¹ * (1 - τb)) • d t + (cvec411 β bb τπ τy τi φπ φx 0 •
        devStack π x πb (xbar β κ πb) t 0 + cvec411 β bb τπ τy τi φπ φx 1 •
        devStack π x πb (xbar β κ πb) t 1 +
          f411 β bb τg τπ τy τi πb (xbar β κ πb) ib G v Yn t) := by
    funext ω
    simp only [cvec411, devStack, f411, taylorRate, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key]

/-- Woodford (2003), p. 314: determinacy of the §4 model — for all bounded adapted disturbances
`(r̂ⁿ, ī, Ĝ, v, Ŷⁿ)` and every initial debt, exactly one bounded adapted equilibrium
`(π, x, b̂)` (`î` and `Ŷ` follow from (1.14) and `Ŷ = x + Ŷⁿ`). -/
def Determinate411 (σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ) : Prop :=
  ∀ rn ib G v Yn : ℕ → Ω → ℝ, BoundedProc rn → 𝔼.Adapted rn → BoundedProc ib →
    𝔼.Adapted ib → BoundedProc G → 𝔼.Adapted G → BoundedProc v → 𝔼.Adapted v →
    BoundedProc Yn → 𝔼.Adapted Yn → ∀ b0 : ℝ,
    ∃! q : ((ℕ → Ω → ℝ) × (ℕ → Ω → ℝ)) × (ℕ → Ω → ℝ),
      Eq411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi rn ib G v Yn b0 q.1.1 q.1.2 q.2 ∧
      𝔼.Adapted q.1.1 ∧ 𝔼.Adapted q.1.2 ∧ 𝔼.Adapted q.2 ∧ BoundedProc q.1.1 ∧
      BoundedProc q.1.2 ∧ BoundedProc q.2

/-- Woodford (2003), (4.5), p. 313: the exogenous part of the debt equation is bounded and
adapted for bounded adapted disturbances. -/
theorem f411_bounded_adapted {β bb τg τπ τy τi πb xb : ℝ} {ib G v Yn : ℕ → Ω → ℝ}
    (h1 : BoundedProc ib) (h2 : 𝔼.Adapted ib) (h3 : BoundedProc G) (h4 : 𝔼.Adapted G)
    (h5 : BoundedProc v) (h6 : 𝔼.Adapted v) (h7 : BoundedProc Yn) (h8 : 𝔼.Adapted Yn) :
    BoundedProc (f411 β bb τg τπ τy τi πb xb ib G v Yn) ∧
      𝔼.Adapted (f411 β bb τg τπ τy τi πb xb ib G v Yn) := by
  obtain ⟨M1, k1⟩ := h1
  obtain ⟨M3, k3⟩ := h3
  obtain ⟨M5, k5⟩ := h5
  obtain ⟨M7, k7⟩ := h7
  refine ⟨⟨|β⁻¹| * (|bb + τπ| * |πb| + |1 - τg| * M3 + |τy| * (|xb| + M7)) +
    |bb - β⁻¹ * τi| * M1 + |β⁻¹| * M5, fun t ω => ?_⟩, fun t => ?_⟩
  · simp only [f411, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have q1 : |-(bb + τπ) * πb + (1 - τg) * G t ω - τy * (xb + Yn t ω)| ≤
        |bb + τπ| * |πb| + |1 - τg| * M3 + |τy| * (|xb| + M7) := by
      refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
      · rw [abs_mul, abs_mul, abs_neg]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (k3 t ω) (abs_nonneg _))
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add le_rfl (k7 t ω)))
          (abs_nonneg _)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left q1 (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (k1 t ω) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (k5 t ω) (abs_nonneg _)
  · simp only [f411, map_add, map_sub, map_smul, 𝔼.const, h2 t, h4 t, h6 t, h8 t]

/-- Woodford (2003), App. C.8: determinacy of the stacked system implies determinacy of the
§4 model. -/
theorem determinate411_of {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ} (hκ : κ ≠ 0)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (h : Determinate3 𝔼 (taylorB β σ κ φπ φx) (cvec411 β bb τπ τy τi φπ φx) (β⁻¹ * (1 - τb))) :
    Determinate411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi := by
  intro rn ib G v Yn a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b0
  obtain ⟨hwb, hwa⟩ := fwdForcing_bounded_adapted 𝔼 (taylorb σ κ φπ φx) a1 a3 a2 a4 πb
  obtain ⟨hfb, hfa⟩ := f411_bounded_adapted 𝔼 (β := β) (bb := bb) (τg := τg) (τπ := τπ)
    (τy := τy) (τi := τi) (πb := πb) (xb := xbar β κ πb) a3 a4 a5 a6 a7 a8 a9 a10
  obtain ⟨⟨z, d⟩, ⟨he, haz, hbz, had, hbd⟩, hu⟩ := h _ _ b0 hwb hwa hfb hfa
  obtain ⟨c1, c2, c3, c4⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := πb) (x0 := xbar β κ πb) hbz haz
  refine ⟨(((ofDevStack πb (xbar β κ πb) z).1, (ofDevStack πb (xbar β κ πb) z).2), d),
    ⟨?_, c1, c2, had, c3, c4, hbd⟩, fun q hq => ?_⟩
  · rw [eq411_iff 𝔼 hκ hΔ, devStack_ofDevStack]
    exact he
  · obtain ⟨hq1, e1, e2, e3, f1, f2, f3⟩ := hq
    have := hu (devStack q.1.1 q.1.2 πb (xbar β κ πb), q.2)
      ⟨(eq411_iff 𝔼 hκ hΔ).mp hq1, devStack_adapted 𝔼 e1 e2 _ _, devStack_bounded f1 f2 _ _, e3, f3⟩
    simp only [Prod.mk.injEq] at this
    obtain ⟨hz, hd⟩ := this
    rw [← hz, ← hd]
    obtain ⟨g1, g2⟩ := devStack_inj (p0 := πb) (x0 := xbar β κ πb)
      (devStack_ofDevStack πb (xbar β κ πb) (devStack q.1.1 q.1.2 πb (xbar β κ πb)))
    rw [g1, g2]

/-- Woodford (2003), p. 314: determinacy of the §4 model implies determinacy of the undisturbed
stacked system (choose `r̂ⁿ = 0`, `ī = π̄`, `Ĝ = Ŷⁿ = 0` and the constant fiscal shock that
cancels the constants in (4.5); `β ≠ 0`). -/
theorem zeroDet_of_determinate411 {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ} (hβ : β ≠ 0)
    (hκ : κ ≠ 0) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (h : Determinate411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi) :
    ZeroDet 𝔼 (taylorB β σ κ φπ φx) (cvec411 β bb τπ τy τi φπ φx) (β⁻¹ * (1 - τb)) := by
  intro b0
  set vs : ℝ := -(bb + τπ) * πb - τy * xbar β κ πb + β * (bb - β⁻¹ * τi) * πb with hvs
  set ib : ℕ → Ω → ℝ := fun _ _ => πb with hib
  set v : ℕ → Ω → ℝ := fun _ _ => vs with hv
  have hw0 : fwdForcing (taylorb σ κ φπ φx) 0 ib πb = 0 := by
    funext t i ω
    fin_cases i <;> simp [fwdForcing, hib]
  have hf0 : f411 β bb τg τπ τy τi πb (xbar β κ πb) ib 0 v 0 = 0 := by
    funext t ω
    simp only [f411, hib, hv, hvs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul]
    field_simp
    ring
  have hc : ∀ (c : ℝ) t, 𝔼.E t (fun _ => c) = fun _ => c := fun c t => 𝔼.const t c
  obtain ⟨q, ⟨hq1, e1, e2, e3, f1, f2, f3⟩, hu⟩ := h 0 ib 0 v 0 ⟨0, fun t ω => by simp⟩
    (fun t => by simp) ⟨|πb|, fun t ω => le_rfl⟩ (fun t => hc πb t) ⟨0, fun t ω => by simp⟩
    (fun t => by simp) ⟨|vs|, fun t ω => le_rfl⟩ (fun t => hc vs t) ⟨0, fun t ω => by simp⟩
    (fun t => by simp) b0
  have hq := (eq411_iff 𝔼 hκ hΔ).mp hq1
  rw [hw0, hf0] at hq
  refine ⟨(devStack q.1.1 q.1.2 πb (xbar β κ πb), q.2),
    ⟨hq, devStack_adapted 𝔼 e1 e2 _ _, devStack_bounded f1 f2 _ _, e3, f3⟩, fun p hp => ?_⟩
  obtain ⟨hp1, g1, g2, g3, g4⟩ := hp
  obtain ⟨c1, c2, c3, c4⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := πb) (x0 := xbar β κ πb) g2 g1
  have hm : Eq411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi 0 ib 0 v 0 b0
      (ofDevStack πb (xbar β κ πb) p.1).1 (ofDevStack πb (xbar β κ πb) p.1).2 p.2 := by
    rw [eq411_iff 𝔼 hκ hΔ, devStack_ofDevStack, hw0, hf0]
    exact hp1
  have := hu (((ofDevStack πb (xbar β κ πb) p.1).1, (ofDevStack πb (xbar β κ πb) p.1).2), p.2)
    ⟨hm, c1, c2, g3, c3, c4, g4⟩
  rw [← this]
  simp only [devStack_ofDevStack]

/-- **Proposition 4.11, locally Ricardian case** (Woodford (2003), p. 314; App. C.8,
pp. 685–686): for `σ, κ > 0`, `0 < β < 1`, `φ_π, φ_x ≥ 0` and a tax rule with `τ_b ≤ 1` and
`τ_b > 1 − β`, the model with debt is determinate iff the Taylor principle (2.7) holds —
the results of Proposition 4.3 apply. -/
theorem prop411_ricardian [Nonempty Ω] {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ} (hσ : 0 < σ)
    (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hτ : τb ≤ 1)
    (hR : 1 - β < τb) :
    Determinate411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi ↔ 1 < φπ + (1 - β) * φx / (4 * κ) := by
  have hΔ : taylorDelta σ κ φπ φx ≠ 0 := by
    unfold taylorDelta; nlinarith [mul_nonneg hσ.le hφx, mul_nonneg (mul_nonneg hκ.le hσ.le) hφπ]
  have hγ : |β⁻¹ * (1 - τb)| < 1 := (ricardian_iff_taub hβ0 hτ).mpr hR
  rw [← taylorLHS_eq, ← taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx]
  constructor
  · intro h
    by_contra hA
    exact not_zeroDet_ricardian 𝔼 hγ hA (zeroDet_of_determinate411 𝔼 hβ0.ne' hκ.ne' hΔ h)
  · intro hA
    exact determinate411_of 𝔼 hκ.ne' hΔ ((determinate3_ricardian 𝔼 hγ).mpr hA)

/-- Woodford (2003), p. 314: `τ_b < 1 − β` (with `0 < β`) makes `γ = β⁻¹(1 − τ_b) > 1`: the
rule is locally non-Ricardian. -/
theorem one_lt_gamma {β τb : ℝ} (hβ0 : 0 < β) (hN : τb < 1 - β) : 1 < |β⁻¹ * (1 - τb)| := by
  have h : 1 < β⁻¹ * (1 - τb) := by
    rw [← div_eq_inv_mul, one_lt_div hβ0]; linarith
  rw [abs_of_pos (by linarith)]
  exact h

/-- **Proposition 4.11, non-Ricardian case with the Taylor principle** (Woodford (2003),
p. 314): the equilibrium is not determinate; indeed, for given disturbances at most one initial
debt admits a bounded equilibrium (`prop411_nonricardian_TP_initial`). -/
theorem prop411_nonricardian_TP [Nonempty Ω] {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hN : τb < 1 - β) (hTP : 1 < φπ + (1 - β) * φx / (4 * κ)) :
    ¬ Determinate411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi := by
  have hΔ : taylorDelta σ κ φπ φx ≠ 0 := by
    unfold taylorDelta; nlinarith [mul_nonneg hσ.le hφx, mul_nonneg (mul_nonneg hκ.le hσ.le) hφπ]
  intro h
  exact not_zeroDet_nonricardian_TP 𝔼 (one_lt_gamma hβ0 hN)
    ((taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx).mpr
      (by rwa [taylorLHS_eq])) (zeroDet_of_determinate411 𝔼 hβ0.ne' hκ.ne' hΔ h)

/-- **Proposition 4.11, non-Ricardian case with the Taylor principle** (Woodford (2003),
p. 314: "for almost all possible initial conditions … no equilibrium in which the paths …
remain forever within small intervals"): for any given disturbances, the set of initial debts
`b̂_{−1}` for which a bounded equilibrium exists has at most one element, so every open set of
initial conditions contains values with no bounded equilibrium. -/
theorem prop411_nonricardian_TP_initial [Nonempty Ω] {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hN : τb < 1 - β) (hTP : 1 < φπ + (1 - β) * φx / (4 * κ)) (rn ib G v Yn : ℕ → Ω → ℝ) :
    {b0 : ℝ | ∃ π x d, Eq411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi rn ib G v Yn b0 π x d ∧
      𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x ∧ BoundedProc d}.Subsingleton := by
  have hΔ : taylorDelta σ κ φπ φx ≠ 0 := by
    unfold taylorDelta; nlinarith [mul_nonneg hσ.le hφx, mul_nonneg (mul_nonneg hκ.le hσ.le) hφπ]
  rintro b0 ⟨π, x, d, he, a1, a2, b1, b2, b3⟩ b0' ⟨π', x', d', he', a1', a2', b1', b2', b3'⟩
  exact nonricardian_TP_initial 𝔼 (one_lt_gamma hβ0 hN)
    ((taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx).mpr
      (by rwa [taylorLHS_eq])) _ _
    ⟨_, d, (eq411_iff 𝔼 hκ.ne' hΔ).mp he, devStack_adapted 𝔼 a1 a2 _ _,
      devStack_bounded b1 b2 _ _, b3⟩
    ⟨_, d', (eq411_iff 𝔼 hκ.ne' hΔ).mp he', devStack_adapted 𝔼 a1' a2' _ _,
      devStack_bounded b1' b2' _ _, b3'⟩

/-- Woodford (2003), App. C.8: the non-degeneracy condition `c·r₂ ≠ 0` in the book's terms,
with `r₂ ∝ (a₀₁, λ₂ − a₀₀)` the eigenvector of the forward matrix for its root `λ₂ > 1`
(equivalently, of the book's matrix (C.19) for its root `λ₂⁻¹` inside the unit circle):
`c_π a₀₁ + c_x(λ₂ − a₀₀) ≠ 0`. -/
theorem nondeg_iff {A : Matrix (Fin 2) (Fin 2) ℝ} {c : Fin 2 → ℝ} {lam1 lam2 : ℝ}
    (hne : lam1 ≠ lam2) (hb : A 0 1 ≠ 0) :
    dot2 c (rvec A lam2 lam1) ≠ 0 ↔ c 0 * A 0 1 + c 1 * (lam2 - A 0 0) ≠ 0 := by
  have h21 : A 0 1 * (lam2 - lam1) ≠ 0 := mul_ne_zero hb (sub_ne_zero.mpr (Ne.symm hne))
  have e : dot2 c (rvec A lam2 lam1) =
      (c 0 * A 0 1 + c 1 * (lam2 - A 0 0)) / (A 0 1 * (lam2 - lam1)) := by
    simp only [dot2, rvec, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [e]
  exact ⟨fun h h0 => h (by rw [h0, zero_div]), fun h h0 => h ((div_eq_zero_iff.mp h0).resolve_right
    h21)⟩

/-- **Proposition 4.11, non-Ricardian case without the Taylor principle — corrected**
(Woodford (2003), p. 314; App. C.8, pp. 685–686): if `τ_b < 1 − β` and the Taylor principle is
violated strictly, the model is determinate **iff** the debt equation loads on the eigen-direction
of the root `λ₂ > 1`: `c_π a₀₁ + c_x(λ₂ − a₀₀) ≠ 0` with `c = cvec411`, `a = taylorB`,
`λ₂ = lamPlus`. The book claims determinacy unconditionally ("generically"); without the
non-degeneracy it fails (`prop411_printed_fails`). -/
theorem prop411_nonricardian_noTP [Nonempty Ω] {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hN : τb < 1 - β) (hrev : φπ + (1 - β) * φx / (4 * κ) < 1) :
    Determinate411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi ↔
      cvec411 β bb τπ τy τi φπ φx 0 * taylorB β σ κ φπ φx 0 1 +
        cvec411 β bb τπ τy τi φπ φx 1 * (lamPlus (tr2 (taylorB β σ κ φπ φx))
          (det2 (taylorB β σ κ φπ φx)) - taylorB β σ κ φπ φx 0 0) ≠ 0 := by
  have hΔpos : 0 < taylorDelta σ κ φπ φx := by
    unfold taylorDelta; nlinarith [mul_nonneg hσ.le hφx, mul_nonneg (mul_nonneg hκ.le hσ.le) hφπ]
  obtain ⟨hsum, hprod, hm0, hm1, hp1⟩ := taylorB_roots hσ hκ hβ0 hβ1 hφπ hφx hrev
  set A := taylorB β σ κ φπ φx with hA
  set l1 := lamMinus (tr2 A) (det2 A)
  set l2 := lamPlus (tr2 A) (det2 A)
  have hne : l1 ≠ l2 := by intro h; linarith
  have hb : A 0 1 ≠ 0 := by
    simp only [hA, taylorB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact div_ne_zero hκ.ne' hΔpos.ne'
  have hS := spectral_of_roots hsum hprod hne hb
  rw [← nondeg_iff hne hb]
  constructor
  · intro h hk
    have hr : rvec A l2 l1 ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp only [rvec, Matrix.cons_val_zero, Pi.zero_apply] at this
      have h21 : l2 - l1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      rcases div_eq_zero_iff.mp this with h1 | h1
      · exact hb h1
      · exact mul_ne_zero hb h21 h1
    exact not_zeroDet_degenerate 𝔼 hr (by rw [abs_of_pos (by linarith)]; linarith)
      (rvec_eigen hsum hprod hne hb) hk (zeroDet_of_determinate411 𝔼 hβ0.ne' hκ.ne'
        hΔpos.ne' h)
  · intro hk
    exact determinate411_of 𝔼 hκ.ne' hΔpos.ne' (determinate3_spectral 𝔼 (one_lt_gamma hβ0 hN)
      hS (by rw [abs_of_pos hm0]; exact hm1) (by rw [abs_of_pos (by linarith)]; exact hp1) hk)

/-- **Proposition 4.11 as printed is false without the non-degeneracy** (Woodford (2003),
p. 314): with `σ = κ = 1`, `β = 1/2`, `φ_π = φ_x = 0` (Taylor principle violated), `b̄ = 1`,
`τ_b = 0` (locally non-Ricardian: `τ_b < 1 − β`), `τ_π = −1`, `τ_y = 0`, `τ_i = 1/2`, the debt
equation does not involve inflation, the gap or the nominal rate at all (`c = 0`), and the
equilibrium is not determinate, contrary to "determinate if and only if the monetary policy rule
violates the Taylor principle". -/
theorem prop411_printed_fails [Nonempty Ω] (πb τg : ℝ) :
    (0 : ℝ) < 1 - 1 / 2 ∧ (0 : ℝ) + (1 - 1 / 2) * 0 / (4 * 1) < 1 ∧
      cvec411 (1 / 2) 1 (-1) 0 (1 / 2) 0 0 = 0 ∧
      ¬ Determinate411 𝔼 1 1 (1 / 2) 0 0 πb 1 0 τg (-1) 0 (1 / 2) := by
  have hc : cvec411 (1 / 2 : ℝ) 1 (-1) 0 (1 / 2) 0 0 = 0 := by
    funext i
    fin_cases i <;> simp [cvec411]
  refine ⟨by norm_num, by norm_num, hc, ?_⟩
  rw [prop411_nonricardian_noTP 𝔼 one_pos one_pos (by norm_num) (by norm_num) le_rfl le_rfl
    (by norm_num) (by norm_num), hc]
  simp

/-- Woodford (2003), (4.5), p. 313: a date-0 fiscal shock `ε` shifts the exogenous part of the
debt equation by `−β⁻¹ε` at date 0. -/
theorem f411_shock {β bb τg τπ τy τi πb xb ε : ℝ} (ib G v Yn : ℕ → Ω → ℝ) :
    f411 β bb τg τπ τy τi πb xb ib G (fun t => v t + fun _ => if t = 0 then ε else 0) Yn =
      fun t => f411 β bb τg τπ τy τi πb xb ib G v Yn t +
        fun _ => if t = 0 then -β⁻¹ * ε else 0 := by
  funext t ω
  simp only [f411, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **Proposition 4.11, non-Ricardian case with the Taylor principle** (Woodford (2003),
p. 314: "for almost all … realizations of the exogenous disturbances"): perturbing the date-0
fiscal shock `v_0` by `ε` leaves at most one `ε` for which a bounded equilibrium exists. -/
theorem prop411_nonricardian_TP_shock [Nonempty Ω] {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hN : τb < 1 - β) (hTP : 1 < φπ + (1 - β) * φx / (4 * κ)) (rn ib G v Yn : ℕ → Ω → ℝ)
    (b0 : ℝ) :
    {ε : ℝ | ∃ π x d, Eq411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi rn ib G
      (fun t => v t + fun _ => if t = 0 then ε else 0) Yn b0 π x d ∧
      𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x ∧ BoundedProc d}.Subsingleton := by
  have hΔ : taylorDelta σ κ φπ φx ≠ 0 := by
    unfold taylorDelta; nlinarith [mul_nonneg hσ.le hφx, mul_nonneg (mul_nonneg hκ.le hσ.le) hφπ]
  rintro ε ⟨π, x, d, he, a1, a2, b1, b2, b3⟩ ε' ⟨π', x', d', he', a1', a2', b1', b2', b3'⟩
  rw [eq411_iff 𝔼 hκ.ne' hΔ, f411_shock] at he he'
  have := nonricardian_TP_shock 𝔼 (one_lt_gamma hβ0 hN)
    ((taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx).mpr
      (by rwa [taylorLHS_eq])) _ _ b0
    ⟨_, d, he, devStack_adapted 𝔼 a1 a2 _ _, devStack_bounded b1 b2 _ _, b3⟩
    ⟨_, d', he', devStack_adapted 𝔼 a1' a2' _ _, devStack_bounded b1' b2' _ _, b3'⟩
  have hb : β⁻¹ ≠ 0 := inv_ne_zero hβ0.ne'
  have : β⁻¹ * ε = β⁻¹ * ε' := by linarith
  exact mul_left_cancel₀ hb this

/-- **Proposition 4.11, locally Ricardian case, indeterminacy** (Woodford (2003), p. 314: "if
the inequality in (2.7) is reversed, equilibrium is indeterminate"): when (2.7) fails, already
with constant disturbances and zero initial debt there are two distinct bounded equilibria. -/
theorem prop411_ricardian_indeterminate [Nonempty Ω] {σ κ β φπ φx πb bb τb τg τπ τy τi : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hτ : τb ≤ 1) (hR : 1 - β < τb) (hTP : ¬ 1 < φπ + (1 - β) * φx / (4 * κ)) :
    ∃ (ib v : ℕ → Ω → ℝ) (π x d π' x' d' : ℕ → Ω → ℝ),
      BoundedProc ib ∧ 𝔼.Adapted ib ∧ BoundedProc v ∧ 𝔼.Adapted v ∧
      Eq411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi 0 ib 0 v 0 0 π x d ∧
      Eq411 𝔼 σ κ β φπ φx πb bb τb τg τπ τy τi 0 ib 0 v 0 0 π' x' d' ∧
      𝔼.Adapted π ∧ 𝔼.Adapted x ∧ 𝔼.Adapted d ∧ BoundedProc π ∧ BoundedProc x ∧
      BoundedProc d ∧ 𝔼.Adapted π' ∧ 𝔼.Adapted x' ∧ 𝔼.Adapted d' ∧ BoundedProc π' ∧
      BoundedProc x' ∧ BoundedProc d' ∧ (π, x) ≠ (π', x') := by
  have hΔ : taylorDelta σ κ φπ φx ≠ 0 := by
    unfold taylorDelta; nlinarith [mul_nonneg hσ.le hφx, mul_nonneg (mul_nonneg hκ.le hσ.le) hφπ]
  have hγ : |β⁻¹ * (1 - τb)| < 1 := (ricardian_iff_taub hβ0 hτ).mpr hR
  have hA : ¬ SchurStable (tr2 (taylorB β σ κ φπ φx)) (det2 (taylorB β σ κ φπ φx)) := by
    rwa [taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx, taylorLHS_eq]
  set vs : ℝ := -(bb + τπ) * πb - τy * xbar β κ πb + β * (bb - β⁻¹ * τi) * πb with hvs
  set ib : ℕ → Ω → ℝ := fun _ _ => πb with hib
  set v : ℕ → Ω → ℝ := fun _ _ => vs with hv
  have hw0 : fwdForcing (taylorb σ κ φπ φx) 0 ib πb = 0 := by
    funext t i ω
    fin_cases i <;> simp [fwdForcing, hib]
  have hf0 : f411 β bb τg τπ τy τi πb (xbar β κ πb) ib 0 v 0 = 0 := by
    funext t ω
    simp only [f411, hib, hv, hvs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul]
    field_simp
    ring
  set c := cvec411 β bb τπ τy τi φπ φx
  set γ := β⁻¹ * (1 - τb)
  obtain ⟨y, hy, hay, hby, hne⟩ := 𝔼.system_not_unique hA (x := 0) (w := 0)
    (fun t i => by simp) (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  obtain ⟨⟨bu, hbu⟩, hau⟩ := coupling_bounded_adapted 𝔼 c hby hay
    (f := 0) ⟨0, fun t ω => by simp⟩ (fun t => by simp)
  have hbu0 : 0 ≤ bu := (abs_nonneg _).trans (hbu 0 (Classical.arbitrary Ω))
  set dy := dRec γ (fun t => c 0 • y t 0 + c 1 • y t 1 + (0 : ℕ → Ω → ℝ) t) (fun _ => 0)
  obtain ⟨c1, c2, c3, c4⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := πb) (x0 := xbar β κ πb) hby hay
  obtain ⟨e1, e2, e3, e4⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := πb) (x0 := xbar β κ πb)
    (z := 0) ⟨0, fun t i ω => by simp⟩ (fun t i => by simp)
  refine ⟨ib, v, (ofDevStack πb (xbar β κ πb) y).1, (ofDevStack πb (xbar β κ πb) y).2, dy,
    (ofDevStack πb (xbar β κ πb) 0).1, (ofDevStack πb (xbar β κ πb) 0).2, 0,
    ⟨|πb|, fun t ω => le_rfl⟩, fun t => 𝔼.const t πb, ⟨|vs|, fun t ω => le_rfl⟩,
    fun t => 𝔼.const t vs, ?_, ?_, c1, c2, dRec_adapted 𝔼 hau, c3, c4,
    ⟨0 + bu / (1 - |γ|), rec_bounded hγ le_rfl hbu0 hbu (fun t => rfl)
      (fun ω => by simp [dy, dRec])⟩, e1, e2, fun t => by simp, e3, e4,
    ⟨0, fun t ω => by simp⟩, fun h => ?_⟩
  · rw [eq411_iff 𝔼 hκ.ne' hΔ, devStack_ofDevStack, hw0, hf0]
    exact ⟨hy, rfl, fun t => rfl⟩
  · rw [eq411_iff 𝔼 hκ.ne' hΔ, devStack_ofDevStack, hw0, hf0]
    exact ⟨fun t i => by simp, by funext ω; rfl, fun t => by funext ω; simp⟩
  · apply hne
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    rw [← devStack_ofDevStack πb (xbar β κ πb) y,
      ← devStack_ofDevStack πb (xbar β κ πb) (0 : ℕ → Fin 2 → Ω → ℝ),
      h1, h2]

end Woodford.NeoWicksellianFramework.Fiscal
