/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.ActivePassive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Links: Cochrane's active/passive fiscal policy and Woodford's Ricardian rules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §§1.8–1.9, pp. 15–19,
compared with Woodford (2003), *Interest and Prices*, Chapter 4, §4, pp. 311–314
(locally Ricardian tax rules) and Chapter 2, §4.1, p. 124 (a Ricardian fiscal rule implies the
transversality condition).

The Woodford material is **restated** from the Woodford Chapter 4 project
(`NeoWicksellianFramework/Fiscal.lean`: `Debt45`, `dRec`, `eq_dRec`, `rec_bounded`,
`rec_unbounded`, `LocallyRicardian`, `locallyRicardian_iff`; `BlanchardKahn.lean`:
`abs_rec_le`) and the Woodford Chapter 2 project (`PriceLevelDetermination/GlobalDynamics.lean`:
`discount`, `ricardian_step`, `ricardian_discounted`, `ricardian_tvc`,
`ricardian_tvc_fails_of_alpha_zero`); nothing is imported from those projects.

## Main results (the links)

* Cochrane's `γ` (the surplus response to the real value of debt, p. 18) plays the role of
  Woodford's `τ_b` in (4.4). `passive_locallyRicardian`: Cochrane's passive response `γ = 1` is
  locally Ricardian for every `β > 0`; `fixed_surplus_not_locallyRicardian`: Cochrane's active
  benchmark `γ = 0` (surpluses that ignore debt) is not, for `0 < β ≤ 1`;
  `locallyRicardian_iff_interval`: locally Ricardian iff `1 − β < τ_b < 1 + β`.
* `two_period_indeterminate_imp_locallyRicardian`: a `γ`-rule that leaves the two-period price
  level indeterminate is locally Ricardian. The converse fails:
  `locallyRicardian_two_period_determinate` (`γ = 1 − β/2` is locally Ricardian yet
  determinate in two periods) — "passive" is the single point `γ = 1` with a last day and an
  interval with an infinite horizon. `not_locallyRicardian_two_period_determinate`: every
  non-Ricardian `γ` gives a determinate two-period price level.
* `passive_is_alpha_one`: Cochrane's passive rule (1.16), `P₁s₁ = B₀`, is Woodford's (4.2)
  Ricardian rule `T = αW − ΔM` with `α = 1` and no money; `alpha_one_debt_retired`: under it
  discounted end-of-period liabilities are zero at every date, so the transversality condition
  holds for every price path, just as (1.14) holds for every `P₁` (`passive_valuation_any_price`);
  `zero_surplus_restricts_prices`: with `α = 0` the transversality condition fails unless
  liabilities are zero, so it restricts prices — the fiscal-theory reading.
-/

namespace Cochrane.TwoPeriodModel.Links

open Filter Topology
open Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.ActivePassive

variable {Ω : Type*}

/-! ### Restated from the Woodford Chapter 4 project -/

/-- Woodford (2003), p. 277 and Prop. C.2, p. 672 (restated from the Woodford Chapter 4
project): a stable scalar recursion `x_{t+1} = λ x_t + u_t` with `|λ| < 1` and bounded `u` stays
bounded; used for Cochrane (2023), §1.9, p. 18. -/
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

/-- Woodford (2003), eq. (4.5), p. 313 (restated from the Woodford Chapter 4 project): the law
of motion of real debt under the tax rule (4.4),
`b̂_t = β⁻¹[(1 − τ_b) b̂_{t−1} − (b̄ + τ_π) π_t + (1 − τ_g) Ĝ_t − τ_y Ŷ_t]
+ (b̄ − β⁻¹τ_i) î_t − β⁻¹ v_t`, with `d_t = b̂_{t−1}`; compared with Cochrane (2023), §1.9,
p. 18. -/
def Debt45 (β bb τb τg τπ τy τi : ℝ) (d π G Y i v : ℕ → Ω → ℝ) : Prop :=
  ∀ t, d (t + 1) = β⁻¹ • ((1 - τb) • d t - (bb + τπ) • π t + (1 - τg) • G t - τy • Y t) +
    (bb - β⁻¹ * τi) • i t - β⁻¹ • v t

/-- Woodford (2003), (4.5), p. 313 (restated from the Woodford Chapter 4 project): the debt
path generated from `d_0` and inputs `u_t` by `d_{t+1} = γ d_t + u_t`; used for Cochrane
(2023), §1.9, p. 18. -/
def dRec (γ : ℝ) (u : ℕ → Ω → ℝ) (d0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d0
  | t + 1 => γ • dRec γ u d0 t + u t

/-- Woodford (2003), (4.5), pp. 313–314 (restated from the Woodford Chapter 4 project): a
solution of `d_{t+1} = γ d_t + u_t` is `dRec`; used for Cochrane (2023), §1.9, p. 18. -/
theorem eq_dRec {γ : ℝ} {u d : ℕ → Ω → ℝ} (hd : ∀ t, d (t + 1) = γ • d t + u t) :
    d = dRec γ u (d 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [hd t, ih]; rfl

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project): for `|γ| < 1`
the recursion `d_{t+1} = γ d_t + u_t` is bounded-input-bounded-state; used for Cochrane (2023),
§1.9, p. 18. -/
theorem rec_bounded {γ B U : ℝ} (hγ : |γ| < 1) {u d : ℕ → Ω → ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hu : ∀ t ω, |u t ω| ≤ U) (hd : ∀ t, d (t + 1) = γ • d t + u t) (h0 : ∀ ω, |d 0 ω| ≤ B) :
    ∀ t ω, |d t ω| ≤ B + U / (1 - |γ|) := by
  intro t ω
  have hq : 0 ≤ U / (1 - |γ|) := div_nonneg hU (by linarith)
  refine (abs_rec_le hγ (u := fun t => u t ω) (x := fun t => d t ω) (fun t => hu t ω) (h0 ω)
    (fun t => by simp [hd t]) t).trans ?_
  exact max_le (by linarith) (by linarith)

/-- Woodford (2003), pp. 313–314 (restated from the Woodford Chapter 4 project): for `|γ| ≥ 1`
the recursion is not bounded-input-bounded-state (`|d_t| ≥ εt` for the inputs
`ε (sign γ)^{t+1}`); used for Cochrane (2023), §1.9, p. 18. -/
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

/-- Woodford (2003), p. 312 (restated from the Woodford Chapter 4 project): a tax rule is
**locally Ricardian** if, substituted into (4.5), it keeps real debt bounded for every small
initial debt and all small paths of `π, Ŷ, î, Ĝ, v`; compared with Cochrane's passive policy,
Cochrane (2023), §1.8–1.9, pp. 17–19. -/
def LocallyRicardian (Ω : Type*) (β bb τb τg τπ τy τi : ℝ) : Prop :=
  ∃ δ > 0, ∀ (b0 : ℝ) (d π Y i G v : ℕ → Ω → ℝ), |b0| ≤ δ →
    (∀ t ω, |π t ω| ≤ δ ∧ |Y t ω| ≤ δ ∧ |i t ω| ≤ δ ∧ |G t ω| ≤ δ ∧ |v t ω| ≤ δ) →
    d 0 = (fun _ => b0) → Debt45 β bb τb τg τπ τy τi d π G Y i v → BoundedProc d

/-- Woodford (2003), p. 313 (restated from the Woodford Chapter 4 project): the tax rule (4.4)
is locally Ricardian iff `|β⁻¹(1 − τ_b)| < 1`; compared with Cochrane (2023), §1.9, p. 18. -/
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

/-! ### Cochrane's `γ` versus Woodford's `τ_b` -/

/-- Cochrane (2023), (1.16), p. 17, and §1.9, p. 18, vs Woodford (2003), (4.4), p. 313:
Cochrane's passive response — surpluses rise one-for-one with the real value of debt,
`γ = τ_b = 1` — is locally Ricardian for every `β > 0` (debt is retired each period). -/
theorem passive_locallyRicardian [Nonempty Ω] {β bb τg τπ τy τi : ℝ} (hβ : 0 < β) :
    LocallyRicardian Ω β bb 1 τg τπ τy τi :=
  (locallyRicardian_iff hβ).mpr (by simp)

/-- Cochrane (2023), §1.8, pp. 17–18, vs Woodford (2003), p. 313: Cochrane's active benchmark,
surpluses that do not respond to the value of debt (`γ = τ_b = 0`), is not locally Ricardian
when `0 < β ≤ 1`. -/
theorem fixed_surplus_not_locallyRicardian [Nonempty Ω] {β bb τg τπ τy τi : ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) : ¬ LocallyRicardian Ω β bb 0 τg τπ τy τi := by
  rw [locallyRicardian_iff hβ, sub_zero, mul_one, abs_of_pos (inv_pos.mpr hβ), not_lt]
  exact one_le_inv₀ hβ |>.mpr hβ1

/-- Woodford (2003), p. 313, in Cochrane's terms (§1.9, p. 18): the debt response `τ_b` is
locally Ricardian ("passive") iff `1 − β < τ_b < 1 + β` (`β > 0`). -/
theorem locallyRicardian_iff_interval [Nonempty Ω] {β bb τb τg τπ τy τi : ℝ} (hβ : 0 < β) :
    LocallyRicardian Ω β bb τb τg τπ τy τi ↔ 1 - β < τb ∧ τb < 1 + β := by
  rw [locallyRicardian_iff hβ, abs_mul, abs_of_pos (inv_pos.mpr hβ), ← div_eq_inv_mul,
    div_lt_one hβ, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Cochrane (2023), §1.9, pp. 18–19, vs Woodford (2003), p. 313: if the `γ`-rule
`s₁ = B₀/P₁* + γ(B₀/P₁ − B₀/P₁*)` leaves the two-period price level indeterminate (no unique
equilibrium; `B₀, P₁* > 0`), the same response `τ_b = γ` is locally Ricardian. -/
theorem two_period_indeterminate_imp_locallyRicardian [Nonempty Ω]
    {β bb γ τg τπ τy τi B0 Pstar : ℝ} (hβ : 0 < β) (hB : 0 < B0) (hPs : 0 < Pstar)
    (h : ¬ ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P) :
    LocallyRicardian Ω β bb γ τg τπ τy τi := by
  have hγ : γ = 1 := by
    by_contra hne
    exact h ((gamma_rule_determinate_iff hB hPs).mpr hne)
  rw [hγ]
  exact passive_locallyRicardian hβ

/-- Cochrane (2023), §1.9, pp. 18–19, vs Woodford (2003), p. 313: the converse fails — with an
infinite horizon "passive" is an interval of responses, with a last day only `γ = 1`: the
response `γ = 1 − β/2` is locally Ricardian, yet the two-period `γ`-rule with it has a unique
equilibrium (`0 < β`, `B₀, P₁* > 0`). -/
theorem locallyRicardian_two_period_determinate [Nonempty Ω] {β bb τg τπ τy τi B0 Pstar : ℝ}
    (hβ : 0 < β) (hB : 0 < B0) (hPs : 0 < Pstar) :
    LocallyRicardian Ω β bb (1 - β / 2) τg τπ τy τi ∧
      ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 (1 - β / 2) B0 Pstar P := by
  refine ⟨(locallyRicardian_iff_interval hβ).mpr ⟨by linarith, by linarith⟩,
    (gamma_rule_determinate_iff hB hPs).mpr ?_⟩
  intro h
  linarith

/-- Cochrane (2023), §1.9, pp. 18–19, vs Woodford (2003), p. 313: every response that is not
locally Ricardian gives a determinate two-period price level (`β, B₀, P₁* > 0`). -/
theorem not_locallyRicardian_two_period_determinate [Nonempty Ω]
    {β bb γ τg τπ τy τi B0 Pstar : ℝ} (hβ : 0 < β) (hB : 0 < B0) (hPs : 0 < Pstar)
    (h : ¬ LocallyRicardian Ω β bb γ τg τπ τy τi) :
    ∃! P : ℝ, 0 < P ∧ B0 / P = gammaRule 1 γ B0 Pstar P := by
  refine (gamma_rule_determinate_iff hB hPs).mpr ?_
  rintro rfl
  exact h (passive_locallyRicardian hβ)

/-! ### Restated from the Woodford Chapter 2 project: a Ricardian rule implies the TVC -/

/-- Woodford (2003), §1, p. 66 (restated from the Woodford Chapter 2 project): the
perfect-foresight discount factor `Q_{t,T} = ∏_{s=t}^{T-1} Q_{s,s+1}`; compared with Cochrane
(2023), (1.16), p. 17. -/
def discount (q : ℕ → ℝ) (t T : ℕ) : ℝ := ∏ s ∈ Finset.Ico t T, q s

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): under
`T_t = αW_t − Δ_tM_t` the government budget gives `Q_{t,t+1}W_{t+1} = (1 − α)W_t`; compared
with Cochrane (2023), (1.16), p. 17. -/
theorem ricardian_step {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (t : ℕ)
    (hgov : q t * W (t + 1) = W t - Tx t - Δ t * M t)
    (hrule : Tx t = α * W t - Δ t * M t) : q t * W (t + 1) = (1 - α) * W t := by
  rw [hgov, hrule]; ring

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): iterating,
`Q_{t,t+n}W_{t+n} = (1 − α)ⁿ W_t`; compared with Cochrane (2023), (1.16), p. 17. -/
theorem ricardian_discounted {q W Tx Δ M : ℕ → ℝ} {α : ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t n : ℕ) :
    discount q t (t + n) * W (t + n) = (1 - α) ^ n * W t := by
  induction n with
  | zero => simp [discount]
  | succ n ih =>
    have hd : discount q t (t + (n + 1)) = discount q t (t + n) * q (t + n) := by
      simp only [discount, ← add_assoc]
      exact Finset.prod_Ico_succ_top (Nat.le_add_right t n) q
    rw [hd, mul_assoc, ← add_assoc, ricardian_step (t + n) (hgov _) (hrule _), ← mul_assoc,
      mul_comm (discount q t (t + n)), mul_assoc, ih]
    ring

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): for
`0 < α ≤ 1`, `Q_{t,T}W_T → 0` whatever the paths of the other variables; compared with
Cochrane (2023), (1.16), p. 17. -/
theorem ricardian_tvc {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t : ℕ) :
    Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T => (1 - α) ^ (T - t) * W t) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - α)
      (by linarith)).comp (tendsto_sub_atTop_nat t)).mul_const (W t)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
  rw [ricardian_discounted hgov hrule t n]
  simp

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): with
`α = 0`, `Q_{t,T}W_T = W_t` for `T ≥ t`, so the transversality condition fails whenever
`W_t ≠ 0`; compared with Cochrane (2023), §1.8, p. 17. -/
theorem ricardian_tvc_fails_of_alpha_zero {q W Tx Δ M : ℕ → ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = 0 * W s - Δ s * M s) (t : ℕ) (hW : W t ≠ 0) :
    ¬ Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) := by
  intro h
  have hconst : Tendsto (fun T => discount q t T * W T) atTop (𝓝 (W t)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop t] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    rw [ricardian_discounted hgov hrule t n]
    simp
  exact hW (tendsto_nhds_unique hconst h)

/-! ### Cochrane's passive rule is Woodford's Ricardian rule with `α = 1` -/

/-- Cochrane (2023), (1.16), p. 17, vs Woodford (2003), (4.2), p. 124: with no money (`M = 0`),
nominal taxes `T = P₁s₁` and maturing liabilities `W = B₀`, Woodford's rule `T = αW − ΔM` with
`α = 1` is exactly Cochrane's passive rule `s₁ = B₀/P₁` (`P₁ ≠ 0`). -/
theorem passive_is_alpha_one {B0 P1 s1 Δ : ℝ} (hP : P1 ≠ 0) :
    P1 * s1 = 1 * B0 - Δ * 0 ↔ s1 = B0 / P1 := by
  rw [one_mul, mul_zero, sub_zero, eq_div_iff hP]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), (1.16), p. 17: under the passive rule the valuation equation (1.14) holds
at every positive price level, the two-period counterpart of Woodford's "the transversality
condition necessarily holds" (`ricardian_tvc`). -/
theorem passive_valuation_any_price (B0 P1 : Ω → ℝ) : Valuation1 B0 P1 (B0 / P1) := rfl

/-- Woodford (2003), (4.2), p. 124 with `α = 1`, in Cochrane's terms ((1.16), p. 17): the
passive rule retires all liabilities each period, `Q_{t,t+1}W_{t+1} = 0`, so discounted
liabilities `Q_{t,T}W_T` vanish for every `T > t` and the transversality condition holds for any
price path. -/
theorem alpha_one_debt_retired {q W Tx Δ M : ℕ → ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = 1 * W s - Δ s * M s) (t n : ℕ) :
    q t * W (t + 1) = 0 ∧ discount q t (t + (n + 1)) * W (t + (n + 1)) = 0 := by
  refine ⟨by rw [ricardian_step t (hgov t) (hrule t)]; ring, ?_⟩
  rw [ricardian_discounted hgov hrule t (n + 1)]
  simp

/-- Cochrane (2023), §1.8, p. 17 ("a passive policy is a choice"), vs Woodford (2003), p. 124:
when taxes do not respond to liabilities (`α = 0`, the analogue of a fixed surplus), the
transversality condition fails at every date with nonzero liabilities: it is not automatically
satisfied but restricts the price path — the valuation equation then determines prices. -/
theorem zero_surplus_restricts_prices {q W Tx Δ M : ℕ → ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = 0 * W s - Δ s * M s) (t : ℕ) :
    Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) → W t = 0 := by
  intro h
  by_contra hW
  exact ricardian_tvc_fails_of_alpha_zero hgov hrule t hW h

end Cochrane.TwoPeriodModel.Links
