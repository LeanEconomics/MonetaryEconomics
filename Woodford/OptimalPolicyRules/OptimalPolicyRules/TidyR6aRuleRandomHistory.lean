/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.IRuleBasic

/-!
# Proposition 8.5 with random pre-sample values

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, (2.1), (3.1), (3.6)–(3.9) (pp. 583–585)
and Proposition 8.5 (p. 584).

`IRuleBasic.rule_determinate` proves Proposition 8.5 for **numbers** `x_{−1}, i_{−1}, i_{−2}`.
Under uncertainty the pre-sample values are random variables known at date `0`
(`𝓕₀`-measurable). Here:

* `lagR`, `RuleR`, `RuleEqmR`: the rule (3.7) and the equilibrium with random pre-sample values;
  `ruleEqmR_const`: for constant ones they are `IRuleBasic.Rule` and `IRuleBasic.RuleEqm`.
* `HomR`: the homogeneous system (no disturbances, no intercept); `eqm_add_hom`, `eqm_sub_eqm`,
  `hom_scale` (a deterministic homogeneous solution times a variable known at `0`),
  `hom_zero` (a bounded adapted homogeneous solution with zero history vanishes).
* **`rule_determinate_random`**: for every bounded adapted `(rⁿ, u)` and every **bounded
  pre-sample values `x_{−1}, i_{−1}, i_{−2}` known at date `0`** there is exactly one bounded
  adapted equilibrium; it is `e⁰ + x_{−1}R¹ + i_{−1}R² + i_{−2}R³`, with `e⁰` the equilibrium
  with zero history and `Rᵏ` the deterministic responses to unit histories.
-/

namespace Woodford.OptimalPolicyRules.TidyR6aRuleRandomHistory

open IRuleBasic

variable {Ω : Type*}

/-- Woodford (2003), (3.6)–(3.7), p. 584: a scalar process lagged once, with a **random**
pre-sample value `z_{−1} = z₀`. -/
def lagR (z0 : Ω → ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => z0
  | t + 1 => z t

/-- Woodford (2003), (3.7): a constant pre-sample value gives `IRuleBasic.lag`. -/
theorem lagR_const (a : ℝ) (z : ℕ → Ω → ℝ) : lagR (fun _ => a) z = lag a z := by
  funext t
  cases t <;> rfl

/-- Woodford (2003), (3.7), p. 584: the rule with random pre-sample values
`x_{−1}, i_{−1}, i_{−2}`. -/
def RuleR (c : Calib) (xm1 im1 im2 : Ω → ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = (fun _ => (1 - rho1 c.β c.σ c.κ) * c.istar) + rho1 c.β c.σ c.κ • lagR im1 i t
    + rho2 c.β • (lagR im1 i t - lagR im2 (lagR im1 i) t) + phiPi c.σ c.κ c.li • π t
    + (phiX c.σ c.lx c.li / 4) • (x t - lagR xm1 x t)

variable (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (2.1), (3.1), (3.7), p. 584: an equilibrium under the rule from date `0`,
with random pre-sample values. -/
def RuleEqmR (c : Calib) (rn u : ℕ → Ω → ℝ) (xm1 im1 im2 : Ω → ℝ) (π x i : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t, AS 𝔼 c u π x t ∧ IS 𝔼 c rn π x i t ∧ RuleR c xm1 im1 im2 π x i t

/-- Woodford (2003), (3.7): with constant pre-sample values the equilibrium is
`IRuleBasic.RuleEqm`. -/
theorem ruleEqmR_const (c : Calib) (rn u : ℕ → Ω → ℝ) (a b d : ℝ) (π x i : ℕ → Ω → ℝ) :
    RuleEqmR 𝔼 c rn u (fun _ => a) (fun _ => b) (fun _ => d) π x i ↔
      RuleEqm 𝔼 c rn u a b d π x i := by
  unfold RuleEqmR RuleEqm RuleR Rule
  simp only [lagR_const]

/-- Woodford (2003), (3.7) without the intercept `(1 − ρ₁)i*`: the homogeneous rule. -/
def RuleHomR (c : Calib) (xm1 im1 im2 : Ω → ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = rho1 c.β c.σ c.κ • lagR im1 i t + rho2 c.β • (lagR im1 i t - lagR im2 (lagR im1 i) t) +
    phiPi c.σ c.κ c.li • π t + (phiX c.σ c.lx c.li / 4) • (x t - lagR xm1 x t)

/-- Woodford (2003), (2.1), (3.1), (3.7): the homogeneous system (no disturbances, no intercept)
with pre-sample values `x_{−1}, i_{−1}, i_{−2}`. -/
def HomR (c : Calib) (xm1 im1 im2 : Ω → ℝ) (π x i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, AS 𝔼 c 0 π x t ∧ IS 𝔼 c 0 π x i t ∧ RuleHomR c xm1 im1 im2 π x i t

/-! ### Linearity -/

/-- Woodford (2003), (3.7) (tool): lags are additive in the pre-sample value and the process. -/
theorem lagR_add (a a' : Ω → ℝ) (z z' : ℕ → Ω → ℝ) (t : ℕ) :
    lagR (a + a') (fun s => z s + z' s) t = lagR a z t + lagR a' z' t := by
  cases t <;> rfl

/-- Woodford (2003), (3.7) (tool): lags commute with differences. -/
theorem lagR_sub (a a' : Ω → ℝ) (z z' : ℕ → Ω → ℝ) (t : ℕ) :
    lagR (a - a') (fun s => z s - z' s) t = lagR a z t - lagR a' z' t := by
  cases t <;> rfl

/-- Woodford (2003), Proposition 8.5 (tool): an equilibrium plus a homogeneous solution is an
equilibrium with the summed pre-sample values. -/
theorem eqm_add_hom {c : Calib} {rn u : ℕ → Ω → ℝ} {a b d a' b' d' : Ω → ℝ}
    {π x i π' x' i' : ℕ → Ω → ℝ} (h : RuleEqmR 𝔼 c rn u a b d π x i)
    (h' : HomR 𝔼 c a' b' d' π' x' i') :
    RuleEqmR 𝔼 c rn u (a + a') (b + b') (d + d') (fun t => π t + π' t) (fun t => x t + x' t)
      (fun t => i t + i' t) := by
  intro t
  obtain ⟨h1, h2, h3⟩ := h t
  obtain ⟨h1', h2', h3'⟩ := h' t
  refine ⟨?_, ?_, ?_⟩
  · unfold AS at h1 h1' ⊢
    rw [map_add]
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h1' ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
    linarith
  · unfold IS at h2 h2' ⊢
    rw [map_add, map_add]
    funext ω
    have e1 := congrFun h2 ω
    have e2 := congrFun h2' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
    linarith
  · unfold RuleR at h3 ⊢
    unfold RuleHomR at h3'
    have e1 := lagR_add b b' i i'
    have e2 : lagR (d + d') (lagR (b + b') fun s => i s + i' s) t =
        lagR d (lagR b i) t + lagR d' (lagR b' i') t := by
      rw [show (lagR (b + b') fun s => i s + i' s) = fun s => lagR b i s + lagR b' i' s from
        funext (e1 ·)]
      exact lagR_add d d' _ _ t
    rw [e1, e2, lagR_add]
    funext ω
    have f1 := congrFun h3 ω
    have f2 := congrFun h3' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f1 f2 ⊢
    linarith

/-- Woodford (2003), Proposition 8.5 (tool): the difference of two equilibria with the same
disturbances solves the homogeneous system with the difference of the pre-sample values. -/
theorem eqm_sub_eqm {c : Calib} {rn u : ℕ → Ω → ℝ} {a b d a' b' d' : Ω → ℝ}
    {π x i π' x' i' : ℕ → Ω → ℝ} (h : RuleEqmR 𝔼 c rn u a b d π x i)
    (h' : RuleEqmR 𝔼 c rn u a' b' d' π' x' i') :
    HomR 𝔼 c (a - a') (b - b') (d - d') (fun t => π t - π' t) (fun t => x t - x' t)
      (fun t => i t - i' t) := by
  intro t
  obtain ⟨h1, h2, h3⟩ := h t
  obtain ⟨h1', h2', h3'⟩ := h' t
  refine ⟨?_, ?_, ?_⟩
  · unfold AS at h1 h1' ⊢
    rw [map_sub]
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h1' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
    linarith
  · unfold IS at h2 h2' ⊢
    rw [map_sub, map_sub]
    funext ω
    have e1 := congrFun h2 ω
    have e2 := congrFun h2' ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
    linarith
  · unfold RuleHomR
    unfold RuleR at h3 h3'
    have e1 := lagR_sub b b' i i'
    have e2 : lagR (d - d') (lagR (b - b') fun s => i s - i' s) t =
        lagR d (lagR b i) t - lagR d' (lagR b' i') t := by
      rw [show (lagR (b - b') fun s => i s - i' s) = fun s => lagR b i s - lagR b' i' s from
        funext (e1 ·)]
      exact lagR_sub d d' _ _ t
    rw [e1, e2, lagR_sub]
    funext ω
    have f1 := congrFun h3 ω
    have f2 := congrFun h3' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f1 f2 ⊢
    linarith

/-! ### Deterministic responses scaled by date-0 information -/

/-- Woodford (2003), p. 540 (tool): a deterministic number times a variable known at every date is
known at every date: `E_t(h r) = h r`. -/
theorem E_scale {h : Ω → ℝ} (hk : ∀ t, 𝔼.E t h = h) (t : ℕ) (r : ℝ) :
    𝔼.E t (fun ω => h ω * r) = fun ω => h ω * r := by
  have e : (fun ω => h ω * r) = r • h := by
    funext ω
    simp [mul_comm]
  rw [e, map_smul, hk]

/-- Woodford (2003), (3.7) (tool): lagging a scaled deterministic sequence. -/
theorem lagR_scale (h : Ω → ℝ) (a : Unit → ℝ) (z : ℕ → Unit → ℝ) (t : ℕ) :
    lagR (fun ω => h ω * a ()) (fun s ω => h ω * z s ()) t =
      fun ω => h ω * lagR a z t () := by
  cases t <;> rfl

/-- Woodford (2003), Proposition 8.5 (tool): a perfect-foresight homogeneous solution, scaled by
a random `h` known at date `0`, is a homogeneous solution under any expectation system, with the
pre-sample values scaled by `h`. -/
theorem hom_scale {c : Calib} {a b d : Unit → ℝ} {π x i : ℕ → Unit → ℝ}
    (hP : HomR perfectForesight c a b d π x i) {h : Ω → ℝ} (hk : ∀ t, 𝔼.E t h = h) :
    HomR 𝔼 c (fun ω => h ω * a ()) (fun ω => h ω * b ()) (fun ω => h ω * d ())
      (fun t ω => h ω * π t ()) (fun t ω => h ω * x t ()) (fun t ω => h ω * i t ()) := by
  intro t
  obtain ⟨h1, h2, h3⟩ := hP t
  have e1 := congrFun h1 ()
  have e2 := congrFun h2 ()
  have e3 := congrFun h3 ()
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 e3
  change π t () = c.κ * x t () + c.β * π (t + 1) () + 0 at e1
  change x t () = x (t + 1) () - c.σ * (i t () - π (t + 1) () - 0) at e2
  refine ⟨?_, ?_, ?_⟩
  · unfold AS
    rw [E_scale 𝔼 hk]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [e1]
    ring
  · unfold IS
    rw [E_scale 𝔼 hk, E_scale 𝔼 hk]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [e2]
    ring
  · unfold RuleHomR
    rw [show (lagR (fun ω => h ω * b ()) fun s ω => h ω * i s ()) =
        fun s ω => h ω * lagR b i s () from funext (lagR_scale h b i ·), lagR_scale h d (lagR b i),
      lagR_scale h a x]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e3]
    ring

/-- Woodford (2003), Proposition 8.5 (tool): a bounded adapted solution of the homogeneous system
with zero pre-sample values is zero (uniqueness of `IRuleBasic.rule_determinate`). -/
theorem hom_zero {c : Calib} (hc : c.Adm) {π x i : ℕ → Ω → ℝ} (hH : HomR 𝔼 c 0 0 0 π x i)
    (ha : 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ 𝔼.Adapted i)
    (hb : BoundedProc π ∧ BoundedProc x ∧ BoundedProc i) : π = 0 ∧ x = 0 ∧ i = 0 := by
  have hz : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hza : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero _
  obtain ⟨s, ⟨hs, hsa, hsb⟩, hu⟩ := rule_determinate 𝔼 c hc hz hza hz hza 0 0 0
  have hR := eqm_add_hom 𝔼 ((ruleEqmR_const 𝔼 c 0 0 0 0 0 _ _ _).mpr hs) hH
  have e0 : (fun _ : Ω => (0 : ℝ)) + 0 = fun _ => 0 := by
    funext ω
    simp
  rw [e0] at hR
  have hR' := (ruleEqmR_const 𝔼 c 0 0 0 0 0 _ _ _).mp hR
  have hsum := hu (fun t => s.1 t + π t, fun t => s.2.1 t + x t, fun t => s.2.2 t + i t)
    ⟨hR', ⟨fun t => by simp only [map_add, hsa.1 t, ha.1 t],
      fun t => by simp only [map_add, hsa.2.1 t, ha.2.1 t],
      fun t => by simp only [map_add, hsa.2.2 t, ha.2.2 t]⟩, ?_⟩
  · have h1 := congrArg Prod.fst hsum
    have h2 := congrArg (fun e => e.2.1) hsum
    have h3 := congrArg (fun e => e.2.2) hsum
    simp only at h1 h2 h3
    refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
    · have := congrFun h1 t
      simpa using this
    · have := congrFun h2 t
      simpa using this
    · have := congrFun h3 t
      simpa using this
  · obtain ⟨⟨K1, h1⟩, ⟨K2, h2⟩, ⟨K3, h3⟩⟩ := hsb
    obtain ⟨⟨L1, g1⟩, ⟨L2, g2⟩, ⟨L3, g3⟩⟩ := hb
    exact ⟨⟨K1 + L1, fun t ω => (abs_add_le _ _).trans (add_le_add (h1 t ω) (g1 t ω))⟩,
      ⟨K2 + L2, fun t ω => (abs_add_le _ _).trans (add_le_add (h2 t ω) (g2 t ω))⟩,
      ⟨K3 + L3, fun t ω => (abs_add_le _ _).trans (add_le_add (h3 t ω) (g3 t ω))⟩⟩

/-! ### Proposition 8.5 with random pre-sample values -/

/-- Woodford (2003), Proposition 8.5 (tool): the deterministic response to a unit pre-sample
value, `P(a, b, d) − P(0, 0, 0)` under perfect foresight. -/
theorem exists_unit_response (c : Calib) (hc : c.Adm) (a b d : ℝ) :
    ∃ r : (ℕ → Unit → ℝ) × (ℕ → Unit → ℝ) × (ℕ → Unit → ℝ),
      HomR perfectForesight c (fun _ => a) (fun _ => b) (fun _ => d) r.1 r.2.1 r.2.2 ∧
        BoundedProc r.1 ∧ BoundedProc r.2.1 ∧ BoundedProc r.2.2 := by
  have hz : BoundedProc (0 : ℕ → Unit → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hza : perfectForesight.Adapted (0 : ℕ → Unit → ℝ) := fun _ => rfl
  obtain ⟨P, ⟨hP, -, hPb⟩, -⟩ := rule_determinate perfectForesight c hc hz hza hz hza a b d
  obtain ⟨P0, ⟨hP0, -, hP0b⟩, -⟩ := rule_determinate perfectForesight c hc hz hza hz hza 0 0 0
  have hH := eqm_sub_eqm perfectForesight ((ruleEqmR_const _ c 0 0 a b d _ _ _).mpr hP)
    ((ruleEqmR_const _ c 0 0 0 0 0 _ _ _).mpr hP0)
  have e : ∀ v : ℝ, (fun _ : Unit => v) - (fun _ => (0 : ℝ)) = fun _ => v := fun v => by
    funext u
    simp
  rw [e, e, e] at hH
  refine ⟨⟨_, _, _⟩, hH, ?_, ?_, ?_⟩
  · obtain ⟨K, hK⟩ := hPb.1
    obtain ⟨L, hL⟩ := hP0b.1
    exact ⟨K + L, fun t ω => (abs_sub _ _).trans (add_le_add (hK t ω) (hL t ω))⟩
  · obtain ⟨K, hK⟩ := hPb.2.1
    obtain ⟨L, hL⟩ := hP0b.2.1
    exact ⟨K + L, fun t ω => (abs_sub _ _).trans (add_le_add (hK t ω) (hL t ω))⟩
  · obtain ⟨K, hK⟩ := hPb.2.2
    obtain ⟨L, hL⟩ := hP0b.2.2
    exact ⟨K + L, fun t ω => (abs_sub _ _).trans (add_le_add (hK t ω) (hL t ω))⟩

/-- Woodford (2003), Proposition 8.5 (tool): a scaled deterministic bounded sequence is
bounded when the scale is bounded. -/
theorem bounded_scale {h : Ω → ℝ} (hb : ∃ K, ∀ ω, |h ω| ≤ K) {r : ℕ → Unit → ℝ}
    (hr : BoundedProc r) : BoundedProc (fun t ω => h ω * r t ()) := by
  obtain ⟨K, hK⟩ := hb
  obtain ⟨L, hL⟩ := hr
  refine ⟨K * L, fun t ω => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hK ω) (hL t ()) (abs_nonneg _) ((abs_nonneg _).trans (hK ω))

/-- **Woodford (2003), Proposition 8.5, p. 584, with random pre-sample values.** For admissible
parameters, every bounded adapted `(rⁿ, u)` and every **bounded pre-sample values
`x_{−1}, i_{−1}, i_{−2}` known at date `0`** (random variables, `E_0 h = h`), there is exactly one
bounded adapted equilibrium of (2.1), (3.1) under the rule (3.7)–(3.9). -/
theorem rule_determinate_random (c : Calib) (hc : c.Adm) {rn u : ℕ → Ω → ℝ}
    (hrb : BoundedProc rn) (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u)
    {xm1 im1 im2 : Ω → ℝ} (hk1 : 𝔼.E 0 xm1 = xm1) (hk2 : 𝔼.E 0 im1 = im1)
    (hk3 : 𝔼.E 0 im2 = im2) (hb1 : ∃ K, ∀ ω, |xm1 ω| ≤ K) (hb2 : ∃ K, ∀ ω, |im1 ω| ≤ K)
    (hb3 : ∃ K, ∀ ω, |im2 ω| ≤ K) :
    ∃! e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      RuleEqmR 𝔼 c rn u xm1 im1 im2 e.1 e.2.1 e.2.2 ∧
        (𝔼.Adapted e.1 ∧ 𝔼.Adapted e.2.1 ∧ 𝔼.Adapted e.2.2) ∧
        (BoundedProc e.1 ∧ BoundedProc e.2.1 ∧ BoundedProc e.2.2) := by
  have known : ∀ {h : Ω → ℝ}, 𝔼.E 0 h = h → ∀ t, 𝔼.E t h = h := fun {h} hk t => by
    rw [← hk, 𝔼.known (Nat.zero_le t)]
  obtain ⟨s, ⟨hs, hsa, hsb⟩, -⟩ := rule_determinate 𝔼 c hc hrb hra hub hua 0 0 0
  obtain ⟨r1, hr1, hr1b⟩ := exists_unit_response c hc 1 0 0
  obtain ⟨r2, hr2, hr2b⟩ := exists_unit_response c hc 0 1 0
  obtain ⟨r3, hr3, hr3b⟩ := exists_unit_response c hc 0 0 1
  have g1 := hom_scale 𝔼 hr1 (known hk1)
  have g2 := hom_scale 𝔼 hr2 (known hk2)
  have g3 := hom_scale 𝔼 hr3 (known hk3)
  have hE := eqm_add_hom 𝔼 (eqm_add_hom 𝔼 (eqm_add_hom 𝔼
    ((ruleEqmR_const 𝔼 c rn u 0 0 0 _ _ _).mpr hs) g1) g2) g3
  have ex : (fun _ : Ω => (0 : ℝ)) + (fun ω => xm1 ω * 1) + (fun ω => im1 ω * 0) +
      (fun ω => im2 ω * 0) = xm1 := by funext ω; simp
  have ei : (fun _ : Ω => (0 : ℝ)) + (fun ω => xm1 ω * 0) + (fun ω => im1 ω * 1) +
      (fun ω => im2 ω * 0) = im1 := by funext ω; simp
  have ed : (fun _ : Ω => (0 : ℝ)) + (fun ω => xm1 ω * 0) + (fun ω => im1 ω * 0) +
      (fun ω => im2 ω * 1) = im2 := by funext ω; simp
  rw [ex, ei, ed] at hE
  set Qπ : ℕ → Ω → ℝ := fun t => ((s.1 t + fun ω => xm1 ω * r1.1 t ()) +
    fun ω => im1 ω * r2.1 t ()) + fun ω => im2 ω * r3.1 t () with hQπ
  set Qx : ℕ → Ω → ℝ := fun t => ((s.2.1 t + fun ω => xm1 ω * r1.2.1 t ()) +
    fun ω => im1 ω * r2.2.1 t ()) + fun ω => im2 ω * r3.2.1 t () with hQx
  set Qi : ℕ → Ω → ℝ := fun t => ((s.2.2 t + fun ω => xm1 ω * r1.2.2 t ()) +
    fun ω => im1 ω * r2.2.2 t ()) + fun ω => im2 ω * r3.2.2 t () with hQi
  have hA : 𝔼.Adapted Qπ ∧ 𝔼.Adapted Qx ∧ 𝔼.Adapted Qi := by
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
    · simp only [hQπ, map_add, hsa.1 t, E_scale 𝔼 (known hk1), E_scale 𝔼 (known hk2),
        E_scale 𝔼 (known hk3)]
    · simp only [hQx, map_add, hsa.2.1 t, E_scale 𝔼 (known hk1), E_scale 𝔼 (known hk2),
        E_scale 𝔼 (known hk3)]
    · simp only [hQi, map_add, hsa.2.2 t, E_scale 𝔼 (known hk1), E_scale 𝔼 (known hk2),
        E_scale 𝔼 (known hk3)]
  have add3 : ∀ {p q w z : ℕ → Ω → ℝ}, BoundedProc p → BoundedProc q → BoundedProc w →
      BoundedProc z → BoundedProc (fun t => p t + q t + w t + z t) :=
    fun {p q w z} ⟨K1, h1⟩ ⟨K2, h2⟩ ⟨K3, h3⟩ ⟨K4, h4⟩ =>
      ⟨K1 + K2 + K3 + K4, fun t ω => by
        simp only [Pi.add_apply]
        exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (h1 t ω) (h2 t ω))) (h3 t ω))) (h4 t ω))⟩
  have hB : BoundedProc Qπ ∧ BoundedProc Qx ∧ BoundedProc Qi :=
    ⟨add3 hsb.1 (bounded_scale hb1 hr1b.1) (bounded_scale hb2 hr2b.1)
        (bounded_scale hb3 hr3b.1),
      add3 hsb.2.1 (bounded_scale hb1 hr1b.2.1) (bounded_scale hb2 hr2b.2.1)
        (bounded_scale hb3 hr3b.2.1),
      add3 hsb.2.2 (bounded_scale hb1 hr1b.2.2) (bounded_scale hb2 hr2b.2.2)
        (bounded_scale hb3 hr3b.2.2)⟩
  refine ⟨⟨Qπ, Qx, Qi⟩, ⟨hE, hA, hB⟩, ?_⟩
  rintro ⟨π', x', i'⟩ ⟨h', ha', hb'⟩
  have hH := eqm_sub_eqm 𝔼 h' hE
  rw [sub_self, sub_self, sub_self] at hH
  have sub_bdd : ∀ {p q : ℕ → Ω → ℝ}, BoundedProc p → BoundedProc q →
      BoundedProc (fun t => p t - q t) := fun {p q} ⟨K1, h1⟩ ⟨K2, h2⟩ =>
    ⟨K1 + K2, fun t ω => (abs_sub _ _).trans (add_le_add (h1 t ω) (h2 t ω))⟩
  obtain ⟨z1, z2, z3⟩ := hom_zero 𝔼 hc hH
    ⟨fun t => by simp only [map_sub, ha'.1 t, hA.1 t],
      fun t => by simp only [map_sub, ha'.2.1 t, hA.2.1 t],
      fun t => by simp only [map_sub, ha'.2.2 t, hA.2.2 t]⟩
    ⟨sub_bdd hb'.1 hB.1, sub_bdd hb'.2.1 hB.2.1, sub_bdd hb'.2.2 hB.2.2⟩
  have u1 : π' = Qπ := funext fun t => sub_eq_zero.mp (congrFun z1 t)
  have u2 : x' = Qx := funext fun t => sub_eq_zero.mp (congrFun z2 t)
  have u3 : i' = Qi := funext fun t => sub_eq_zero.mp (congrFun z3 t)
  rw [u1, u2, u3]

/-! ### Optimality with random pre-sample values -/

/-- Woodford (2003), (3.3), p. 584, with random pre-sample multipliers `φ_{1,−1}, φ_{2,−1}`. -/
def FOC3R (c : Calib) (π φ1 φ2 : ℕ → Ω → ℝ) (φ1h φ2h : Ω → ℝ) (t : ℕ) : Prop :=
  π t - (c.σ / c.β) • lagR φ1h φ1 t + φ2 t - lagR φ2h φ2 t = 0

/-- Woodford (2003), (3.4), p. 584, with a random pre-sample multiplier `φ_{1,−1}`. -/
def FOC4R (c : Calib) (x φ1 φ2 : ℕ → Ω → ℝ) (φ1h : Ω → ℝ) (t : ℕ) : Prop :=
  c.lx • (x t - fun _ => c.xstar) + φ1 t - c.β⁻¹ • lagR φ1h φ1 t - c.κ • φ2 t = 0

/-- Woodford (2003), (3.3)–(3.5), p. 584, with random pre-sample multipliers. -/
def FOCR (c : Calib) (π x i φ1 φ2 : ℕ → Ω → ℝ) (φ1h φ2h : Ω → ℝ) : Prop :=
  ∀ t, FOC3R c π φ1 φ2 φ1h φ2h t ∧ FOC4R c x φ1 φ2 φ1h t ∧ FOC5 c i φ1 t

/-- **Woodford (2003), §3.1, pp. 584–585: the Lagrangian identity with random pre-sample
multipliers** (restated from `IRuleBasic.lagrangian_identity`, with `lagR`; the pre-sample
multipliers only multiply `π'₀ − π₀` and `x'₀ − x₀`, which vanish). -/
theorem lagrangian_identityR (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut)
    {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : Ω → ℝ}
    (hf : Feasible 𝔼 c rn u π x i) (hfoc : FOCR c π x i φ1 φ2 φ1h φ2h)
    (hh1 : ∃ K, ∀ ω, |φ1h ω| ≤ K) (hh2 : ∃ K, ∀ ω, |φ2h ω| ≤ K)
    (hφ1a : 𝔼.Adapted φ1) (hφ2a : 𝔼.Adapted φ2)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    (hφ1b : BoundedProc φ1) (hφ2b : BoundedProc φ2)
    {π' x' i' : ℕ → Ω → ℝ} (hf' : Feasible 𝔼 c rn u π' x' i')
    (hπb' : BoundedProc π') (hxb' : BoundedProc x') (hib' : BoundedProc i')
    (h0 : π' 0 = π 0) (hx0 : x' 0 = x 0) (ω : Ω) :
    Jloss 𝔼 c π' x' i' ω = Jloss 𝔼 c π x i ω +
      ∑' t, c.β ^ t * 𝔼.E 0 (fun ω' => (π' t ω' - π t ω') ^ 2
        + c.lx * (x' t ω' - x t ω') ^ 2 + c.li * (i' t ω' - i t ω') ^ 2) ω := by
  have hc' := hc
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩ := hc'
  set dπ : ℕ → Ω → ℝ := fun t => π' t - π t with hdπ
  set dx : ℕ → Ω → ℝ := fun t => x' t - x t with hdx
  set di : ℕ → Ω → ℝ := fun t => i' t - i t with hdi
  set Sq : ℕ → Ω → ℝ := fun t ω' => (π' t ω' - π t ω') ^ 2
    + c.lx * (x' t ω' - x t ω') ^ 2 + c.li * (i' t ω' - i t ω') ^ 2 with hSq
  set G : ℕ → Ω → ℝ := fun t => π t * dπ t + c.lx • ((x t - fun _ => c.xstar) * dx t)
    + c.li • ((i t - fun _ => c.istar) * di t) with hG
  set b : ℕ → Ω → ℝ := fun t => c.β⁻¹ • (lagR φ1h φ1 t * (c.σ • dπ t + dx t))
    + lagR φ2h φ2 t * dπ t with hb
  -- (1) the loss difference
  have hL : ∀ t, periodLoss c π' x' i' t = periodLoss c π x i t + (2 : ℝ) • G t + Sq t := by
    intro t
    funext ω'
    simp only [periodLoss, hG, hSq, hdπ, hdx, hdi, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  -- (2) the first-order conditions and the constraints
  have hGb : ∀ t, G t = b t - (c.β • (φ2 t * 𝔼.E t (dπ (t + 1)))
      + φ1 t * (𝔼.E t (dx (t + 1)) + c.σ • 𝔼.E t (dπ (t + 1)))) := by
    intro t
    funext ω'
    obtain ⟨f3, f4, f5⟩ := hfoc t
    have f3 := congrFun f3 ω'
    have f4 := congrFun f4 ω'
    have f5 := congrFun f5 ω'
    have a1 := congrFun (hf t).1 ω'
    have a2 := congrFun (hf' t).1 ω'
    have s1 := congrFun (hf t).2 ω'
    have s2 := congrFun (hf' t).2 ω'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at f3 f4 f5 a1 a2 s1 s2
    simp only [hG, hb, hdπ, hdx, hdi, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul]
    have hβne : c.β ≠ 0 := hβ0.ne'
    linear_combination (norm := (field_simp; ring)) (π' t ω' - π t ω') * f3
      + (x' t ω' - x t ω') * f4 + (i' t ω' - i t ω') * f5
      - φ2 t ω' * (a2 - a1) - φ1 t ω' * (s2 - s1)
  -- (3) the pull-out step: `E₀ c'_t = β E₀ b_{t+1}`
  have hc' : ∀ t, 𝔼.E 0 (c.β • (φ2 t * 𝔼.E t (dπ (t + 1)))
      + φ1 t * (𝔼.E t (dx (t + 1)) + c.σ • 𝔼.E t (dπ (t + 1)))) = c.β • 𝔼.E 0 (b (t + 1)) := by
    intro t
    have e1 : c.β • (φ2 t * 𝔼.E t (dπ (t + 1)))
        + φ1 t * (𝔼.E t (dx (t + 1)) + c.σ • 𝔼.E t (dπ (t + 1))) =
        𝔼.E t (c.β • (φ2 t * dπ (t + 1)) + φ1 t * (dx (t + 1) + c.σ • dπ (t + 1))) := by
      rw [map_add, map_smul, hpo t _ _ (hφ2a t), hpo t _ _ (hφ1a t), map_add, map_smul]
    have e2 : c.β • (φ2 t * dπ (t + 1)) + φ1 t * (dx (t + 1) + c.σ • dπ (t + 1)) =
        c.β • b (t + 1) := by
      have hβne : c.β ≠ 0 := hβ0.ne'
      funext ω'
      simp only [hb, lagR, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      field_simp
      ring
    rw [e1, 𝔼.tower (Nat.zero_le t), e2, map_smul]
  -- (4) the initial term vanishes by the commitments (3.6)
  have hb0 : b 0 = 0 := by
    funext ω'
    simp only [hb, hdπ, hdx, lagR, h0, hx0, sub_self, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  -- (5) bounds
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπ', hMπ'⟩ := hπb'
  obtain ⟨Mx', hMx'⟩ := hxb'
  obtain ⟨M1, hM1⟩ := hφ1b
  obtain ⟨M2, hM2⟩ := hφ2b
  obtain ⟨K1, hK1⟩ := hh1
  obtain ⟨K2, hK2⟩ := hh2
  set L1M := max M1 K1
  set L2M := max M2 K2
  have hl1 : ∀ t ω', |lagR φ1h φ1 t ω'| ≤ L1M := by
    intro t ω'
    cases t with
    | zero => exact (hK1 ω').trans (le_max_right _ _)
    | succ t => exact (hM1 t ω').trans (le_max_left _ _)
  have hl2 : ∀ t ω', |lagR φ2h φ2 t ω'| ≤ L2M := by
    intro t ω'
    cases t with
    | zero => exact (hK2 ω').trans (le_max_right _ _)
    | succ t => exact (hM2 t ω').trans (le_max_left _ _)
  have hdπb : ∀ t ω', |dπ t ω'| ≤ Mπ' + Mπ := fun t ω' =>
    (abs_sub _ _).trans (add_le_add (hMπ' t ω') (hMπ t ω'))
  have hdxb : ∀ t ω', |dx t ω'| ≤ Mx' + Mx := fun t ω' =>
    (abs_sub _ _).trans (add_le_add (hMx' t ω') (hMx t ω'))
  set MB := |c.β⁻¹| * (L1M * (|c.σ| * (Mπ' + Mπ) + (Mx' + Mx))) + L2M * (Mπ' + Mπ)
  have hbb : ∀ t ω', |b t ω'| ≤ MB := by
    intro t ω'
    simp only [hb, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul (hl1 t ω') ?_ (abs_nonneg _)
        ((abs_nonneg _).trans (hl1 t ω'))) (abs_nonneg _)
      refine (abs_add_le _ _).trans (add_le_add ?_ (hdxb t ω'))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdπb t ω') (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul (hl2 t ω') (hdπb t ω') (abs_nonneg _) ((abs_nonneg _).trans (hl2 t ω'))
  -- (6) summing
  set y : ℕ → ℝ := fun t => c.β ^ t * 𝔼.E 0 (b t) ω with hy
  have hyb : ∀ t, |y t| ≤ MB * c.β ^ t := by
    intro t
    simp only [hy, abs_mul, abs_pow, abs_of_pos hβ0]
    rw [mul_comm MB]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hbb t) 0 ω) (pow_nonneg hβ0.le t)
  have key : ∀ t, c.β ^ t * 𝔼.E 0 (periodLoss c π' x' i' t) ω =
      c.β ^ t * 𝔼.E 0 (periodLoss c π x i t) ω + 2 * (y t - y (t + 1))
        + c.β ^ t * 𝔼.E 0 (Sq t) ω := by
    intro t
    have e := congrFun (congrArg (𝔼.E 0) (hL t)) ω
    rw [map_add, map_add, map_smul, hGb t, map_sub, hc' t] at e
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
    rw [e]
    simp only [hy, pow_succ]
    ring
  obtain ⟨ML, hML⟩ := periodLoss_bounded c hc ⟨Mπ, hMπ⟩ ⟨Mx, hMx⟩ hib
  obtain ⟨ML', hML'⟩ := periodLoss_bounded c hc ⟨Mπ', hMπ'⟩ ⟨Mx', hMx'⟩ hib'
  have s1 := summable_disc 𝔼 hβ0.le hβ1 hML ω
  have s1' := summable_disc 𝔼 hβ0.le hβ1 hML' ω
  have s2 : Summable (fun t => y t - y (t + 1)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left
      (2 * MB)) (fun t => ?_)
    rw [Real.norm_eq_abs]
    have hp : c.β ^ (t + 1) ≤ c.β ^ t := pow_le_pow_of_le_one hβ0.le hβ1.le (Nat.le_succ t)
    have hMB : 0 ≤ MB := (abs_nonneg _).trans (hbb 0 ω)
    calc |y t - y (t + 1)| ≤ |y t| + |y (t + 1)| := abs_sub _ _
      _ ≤ MB * c.β ^ t + MB * c.β ^ t :=
          add_le_add (hyb t) ((hyb (t + 1)).trans (mul_le_mul_of_nonneg_left hp hMB))
      _ = 2 * MB * c.β ^ t := by ring
  have s3 : Summable (fun t => c.β ^ t * 𝔼.E 0 (Sq t) ω) := by
    have : (fun t => c.β ^ t * 𝔼.E 0 (Sq t) ω) = fun t =>
        c.β ^ t * 𝔼.E 0 (periodLoss c π' x' i' t) ω
          - c.β ^ t * 𝔼.E 0 (periodLoss c π x i t) ω - 2 * (y t - y (t + 1)) := by
      funext t
      rw [key t]
      ring
    rw [this]
    exact (s1'.sub s1).sub (s2.mul_left 2)
  have htel : ∑' t, (y t - y (t + 1)) = 0 := by
    rw [tsum_telescope hβ0.le hβ1 (C := MB) hyb]
    simp [hy, hb0]
  unfold Jloss
  rw [tsum_congr key, (s1.add (s2.mul_left 2)).tsum_add s3, s1.tsum_add (s2.mul_left 2),
    tsum_mul_left, htel]
  ring


/-- **Woodford (2003), §3.1: Lagrangian sufficiency with random pre-sample multipliers.** -/
theorem plan_optimalR (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut)
    {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : Ω → ℝ}
    (hf : Feasible 𝔼 c rn u π x i) (hfoc : FOCR c π x i φ1 φ2 φ1h φ2h)
    (hh1 : ∃ K, ∀ ω, |φ1h ω| ≤ K) (hh2 : ∃ K, ∀ ω, |φ2h ω| ≤ K)
    (hφ1a : 𝔼.Adapted φ1) (hφ2a : 𝔼.Adapted φ2)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    (hφ1b : BoundedProc φ1) (hφ2b : BoundedProc φ2)
    {π' x' i' : ℕ → Ω → ℝ} (hf' : Feasible 𝔼 c rn u π' x' i')
    (hπb' : BoundedProc π') (hxb' : BoundedProc x') (hib' : BoundedProc i')
    (h0 : π' 0 = π 0) (hx0 : x' 0 = x 0) : Jloss 𝔼 c π x i ≤ Jloss 𝔼 c π' x' i' := by
  intro ω
  rw [lagrangian_identityR 𝔼 c hc hpo hf hfoc hh1 hh2 hφ1a hφ2a hπb hxb hib hφ1b hφ2b hf' hπb'
    hxb' hib' h0 hx0 ω]
  have hlx := hc.2.2.2.2.1
  have hli := hc.2.2.2.2.2
  refine le_add_of_nonneg_right (tsum_nonneg fun t => mul_nonneg (pow_nonneg hc.1.le t) ?_)
  have hm := 𝔼.mono 0 (x := fun _ => (0 : ℝ))
    (y := fun ω' => (π' t ω' - π t ω') ^ 2 + c.lx * (x' t ω' - x t ω') ^ 2
      + c.li * (i' t ω' - i t ω') ^ 2) (fun ω' => by positivity)
  rw [𝔼.const] at hm
  exact hm ω

/-- Woodford (2003), p. 584: the random pre-sample multiplier `φ_{1,−1} = −(λ_i/σ)(i_{−1} − i*)`. -/
noncomputable def mult1hR (c : Calib) (im1 : Ω → ℝ) : Ω → ℝ := fun ω => mult1h c (im1 ω)

/-- Woodford (2003), p. 584: `φ_{2t}` read off (3.4) with a random pre-sample `i_{−1}`. -/
noncomputable def mult2R (c : Calib) (im1 : Ω → ℝ) (x i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => c.κ⁻¹ • (c.lx • (x t - fun _ => c.xstar) + mult1 c i t
    - c.β⁻¹ • lagR (mult1hR c im1) (mult1 c i) t)

/-- Woodford (2003), p. 585: the random pre-sample multiplier `φ_{2,−1}` from the random
history. -/
noncomputable def mult2hR (c : Calib) (xm1 im1 im2 : Ω → ℝ) : Ω → ℝ :=
  fun ω => mult2h c (xm1 ω) (im1 ω) (im2 ω)

/-- Woodford (2003), p. 584 (tool): the lagged first multiplier, random history. -/
theorem lag_mult1R (c : Calib) (im1 : Ω → ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lagR (mult1hR c im1) (mult1 c i) t ω = -(c.li / c.σ) * (lagR im1 i t ω - c.istar) := by
  cases t with
  | zero => rfl
  | succ t => simp [lagR, mult1, smul_eq_mul]

/-- Woodford (2003), p. 584 (tool): the lagged second multiplier, random history. -/
theorem lag_mult2R (c : Calib) (xm1 im1 im2 : Ω → ℝ) (x i : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lagR (mult2hR c xm1 im1 im2) (mult2R c im1 x i) t ω =
      c.κ⁻¹ * (c.lx * (lagR xm1 x t ω - c.xstar) + -(c.li / c.σ) * (lagR im1 i t ω - c.istar)
        - c.β⁻¹ * (-(c.li / c.σ) * (lagR im2 (lagR im1 i) t ω - c.istar))) := by
  cases t with
  | zero => rfl
  | succ t =>
    change mult2R c im1 x i t ω = _
    simp only [mult2R, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [lag_mult1R]
    simp [lagR, mult1, smul_eq_mul]

/-- Woodford (2003), (3.7)–(3.9), p. 584 (the elimination of the multipliers, random history):
the rule holds at `t` iff (3.3) does with the multipliers read off (3.4)–(3.5). -/
theorem rule_iff_foc3R (c : Calib) (hβ : c.β ≠ 0) (hσ : c.σ ≠ 0) (hκ : c.κ ≠ 0)
    (hli : c.li ≠ 0) (xm1 im1 im2 : Ω → ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) :
    RuleR c xm1 im1 im2 π x i t ↔
      FOC3R c π (mult1 c i) (mult2R c im1 x i) (mult1hR c im1) (mult2hR c xm1 im1 im2) t := by
  unfold RuleR FOC3R
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [lag_mult1R, lag_mult2R]
  simp only [mult2R, mult1, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  rw [lag_mult1R]
  exact rule_foc3_real c hβ hσ hκ hli _ _ _ _ _ _

/-- Woodford (2003), (3.4), p. 584: `φ₂` read off (3.4) satisfies (3.4), random history. -/
theorem foc4_multR (c : Calib) (hκ : c.κ ≠ 0) (im1 : Ω → ℝ) (x i : ℕ → Ω → ℝ) (t : ℕ) :
    FOC4R c x (mult1 c i) (mult2R c im1 x i) (mult1hR c im1) t := by
  unfold FOC4R mult2R
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

/-- Woodford (2003), p. 584: with `i_{−1}` known at date `0`, the multiplier `φ₂` of an adapted
plan is adapted. -/
theorem mult2R_adapted (c : Calib) {im1 : Ω → ℝ} (hk : 𝔼.E 0 im1 = im1) {x i : ℕ → Ω → ℝ}
    (hx : 𝔼.Adapted x) (hi : 𝔼.Adapted i) : 𝔼.Adapted (mult2R c im1 x i) := by
  have hl : ∀ t, 𝔼.E t (lagR (mult1hR c im1) (mult1 c i) t) =
      lagR (mult1hR c im1) (mult1 c i) t := by
    intro t
    cases t with
    | zero =>
      have e : lagR (mult1hR c im1) (mult1 c i) 0 =
          (-(c.li / c.σ)) • im1 + fun _ => c.li / c.σ * c.istar := by
        funext ω
        simp only [lagR, mult1hR, mult1h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, map_add, map_smul, hk, 𝔼.const]
    | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (mult1_adapted 𝔼 c hi t)
  intro t
  simp only [mult2R, map_smul, map_sub, map_add, hx t, 𝔼.const, mult1_adapted 𝔼 c hi t, hl t]

/-- Woodford (2003), p. 584: the multipliers of a bounded plan with bounded random history are
bounded. -/
theorem mult_bounded (c : Calib) {im1 : Ω → ℝ} (hb : ∃ K, ∀ ω, |im1 ω| ≤ K)
    {x i : ℕ → Ω → ℝ} (hx : BoundedProc x) (hi : BoundedProc i) :
    BoundedProc (mult1 c i) ∧ BoundedProc (mult2R c im1 x i) ∧
      ∃ K, ∀ ω, |mult1hR c im1 ω| ≤ K := by
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨Mi, hMi⟩ := hi
  obtain ⟨K, hK⟩ := hb
  set B1 := |c.li / c.σ| * (max Mi K + |c.istar|) with hB1
  have h1 : ∀ t ω, |mult1 c i t ω| ≤ B1 := by
    intro t ω
    simp only [mult1, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg, hB1]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add
      ((hMi t ω).trans (le_max_left _ _)) le_rfl)) (abs_nonneg _)
  have hh : ∀ ω, |mult1hR c im1 ω| ≤ B1 := by
    intro ω
    simp only [mult1hR, mult1h, abs_mul, abs_neg, hB1]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add
      ((hK ω).trans (le_max_right _ _)) le_rfl)) (abs_nonneg _)
  have hl1 : ∀ t ω, |lagR (mult1hR c im1) (mult1 c i) t ω| ≤ B1 := by
    intro t ω
    cases t with
    | zero => exact hh ω
    | succ t => exact h1 t ω
  refine ⟨⟨B1, h1⟩, ⟨|c.κ⁻¹| * (|c.lx| * (Mx + |c.xstar|) + B1 + |c.β⁻¹| * B1), fun t ω => ?_⟩,
    ⟨B1, hh⟩⟩
  simp only [mult2R, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ (h1 t ω))) ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMx t ω) le_rfl))
      (abs_nonneg _)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hl1 t ω) (abs_nonneg _)

/-- **Woodford (2003), §3.1, p. 585, with random pre-sample values: the rule is optimal from a
timeless perspective.** Every bounded adapted equilibrium under (3.7)–(3.9) with bounded
pre-sample values known at date `0` minimises the expected discounted loss among all bounded
adapted feasible plans with the same `π₀`, `x₀` (pull-out property assumed). -/
theorem rule_eqm_optimal_random (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut)
    {rn u π x i : ℕ → Ω → ℝ} {xm1 im1 im2 : Ω → ℝ} (he : RuleEqmR 𝔼 c rn u xm1 im1 im2 π x i)
    (hk2 : 𝔼.E 0 im1 = im1) (hb1 : ∃ K, ∀ ω, |xm1 ω| ≤ K) (hb2 : ∃ K, ∀ ω, |im1 ω| ≤ K)
    (hb3 : ∃ K, ∀ ω, |im2 ω| ≤ K) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hia : 𝔼.Adapted i) (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i) :
    OptimalGiven 𝔼 c rn u (π 0) (x 0) π x i := by
  have hc' := hc
  obtain ⟨hβ0, -, hσ, hκ, -, hli⟩ := hc'
  have hfoc : FOCR c π x i (mult1 c i) (mult2R c im1 x i) (mult1hR c im1)
      (mult2hR c xm1 im1 im2) := fun t =>
    ⟨(rule_iff_foc3R c hβ0.ne' hσ.ne' hκ.ne' hli.ne' xm1 im1 im2 π x i t).mp (he t).2.2,
      foc4_multR c hκ.ne' im1 x i t, foc5_mult c hσ.ne' i t⟩
  obtain ⟨hb1', hb2', hh1⟩ := mult_bounded c hb2 hxb hib
  have hh2 : ∃ K, ∀ ω, |mult2hR c xm1 im1 im2 ω| ≤ K := by
    obtain ⟨K1, g1⟩ := hb1
    obtain ⟨K2, g2⟩ := hb2
    obtain ⟨K3, g3⟩ := hb3
    refine ⟨|c.κ⁻¹| * (|c.lx| * (K1 + |c.xstar|) + |c.li / c.σ| * (K2 + |c.istar|) +
      |c.β⁻¹| * (|c.li / c.σ| * (K3 + |c.istar|))), fun ω => ?_⟩
    simp only [mult2hR, mult2h, mult1h, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (g1 ω) le_rfl))
        (abs_nonneg _)
    · rw [abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (g2 ω) le_rfl))
        (abs_nonneg _)
    · rw [abs_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
        (add_le_add (g3 ω) le_rfl)) (abs_nonneg _)) (abs_nonneg _)
  refine ⟨fun t => ⟨(he t).1, (he t).2.1⟩, ⟨hπa, hxa, hia⟩, ⟨hπb, hxb, hib⟩, rfl, rfl, ?_⟩
  intro π' x' i' hf' _ ⟨hπb', hxb', hib'⟩ h0 hx0
  exact plan_optimalR 𝔼 c hc hpo (fun t => ⟨(he t).1, (he t).2.1⟩) hfoc hh1 hh2
    (mult1_adapted 𝔼 c hia) (mult2R_adapted 𝔼 c hk2 hxa hia) hπb hxb hib hb1' hb2' hf' hπb'
    hxb' hib' h0 hx0

end Woodford.OptimalPolicyRules.TidyR6aRuleRandomHistory
