/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5aMeasBK
import OptimalPolicyRules.TidyR5aLambdaXZero

/-!
# The rule system of p. 593 at `λₓ = 0` with conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 8, §3.2, p. 593: the implicit instrument rule
(3.16)/(3.21) of the inflation-inertia model, together with (2.6) and (3.1), on every filtered
probability space with Mathlib's conditional expectation, for essentially bounded adapted plans
(`RuleSolM`, with history `HistoryM`). This is the measure-theoretic version of
`TidyR5aLambdaXZero`.

* `rule_system_uniqueM` (**uniqueness, every `λₓ ≥ 0`, every `γ`**): two solutions with the same
  disturbances and history agree a.s. at every date `≥ 1`. The proof is a **forecast transfer**
  (`forecast_zero`): at almost every outcome the conditional forecasts `m ↦ E_n d_{n−2+m}` of the
  difference of two solutions solve the perfect-foresight rule system with zero history, hence
  vanish by `InflationInertiaRules.rule_system_unique`.
* `rule_system_existsUniqueM_lx0` (**existence and uniqueness at `λₓ = 0`, `0 ≤ γ ≤ 1`**): the
  rule system is a linear expectational system in `(π, x, i)` with predetermined lags; its
  stacked form satisfies the Blanchard–Kahn conditions (`PosM.existsM` for `0 < γ ≤ 1`,
  `ZeroM.existsM` for `γ = 0`, with the eigenvalue counts of `TidyR5aLambdaXZero`), so
  `TidyR5aMeasBK.m_bk_exists` gives a solution, read back by `PosM.eqsM` / `ZeroM.eqsM`.

Not covered: existence with conditional expectations for `λₓ > 0` (uniqueness is covered).
-/

namespace Woodford.OptimalPolicyRules.TidyR5aLambdaXZeroMeasure

open MeasureTheory Filter Matrix
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov
open BKInvariantSplit TidyR5aMeasBK
open InflationInertiaRules (ALi qtil)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The rule system with conditional expectations -/

/-- Woodford (2003), eq. (2.6) (corrected, Ch. 3 (3.6)), p. 562, a.s. at date `k`:
`π_k − γπ_{k−1} = κx_k + βE_k[π_{k+1} − γπ_k] + u_k`. -/
def ASm (S : MeasExpectationSystem Ω) (β γ κ : ℝ) (u π x : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, π k ω - γ * π (k - 1) ω =
    κ * x k ω + β * S.E k (fun ω' => π (k + 1) ω' - γ * π k ω') ω + u k ω

/-- Woodford (2003), eq. (3.1), p. 583, a.s. at date `k`:
`x_k = E_kx_{k+1} − σ(i_k − E_kπ_{k+1} − rⁿ_k)`. -/
def ISm (S : MeasExpectationSystem Ω) (σ : ℝ) (rn π x i : ℕ → Ω → ℝ) (k : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, x k ω = S.E k (x (k + 1)) ω - σ * (i k ω - S.E k (π (k + 1)) ω - rn k ω)

/-- Woodford (2003), eq. (3.18), p. 593, with Mathlib's conditional expectation:
`f_k = q̃_k − βγE_kq̃_{k+1}`. -/
noncomputable def fbigM (S : MeasExpectationSystem Ω) (β γ κ σ lamx lami : ℝ)
    (π x : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  qtil γ κ σ lamx lami π x k ω - β * γ * S.E k (qtil γ κ σ lamx lami π x (k + 1)) ω

/-- Woodford (2003), eq. (3.16)/(3.21), p. 594, a.s. at date `n = t + 2`:
`E_n[A(L)ı̂_{n+1}] = −f̂_n`. -/
def EulerM (S : MeasExpectationSystem Ω) (β γ κ σ : ℝ) (ı f : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ᵐ ω ∂S.μ, S.E (t + 2) (ALi β γ κ σ ı t) ω = -f (t + 2) ω

/-- Woodford (2003), Ch. 8 (bounded plans), fn 6, p. 539: an essentially bounded process. -/
def BndM (S : MeasExpectationSystem Ω) (g : ℕ → Ω → ℝ) : Prop :=
  ∃ C, ∀ k, ∀ᵐ ω ∂S.μ, |g k ω| ≤ C

/-- Woodford (2003), p. 537: an adapted process (`g_k` is `𝓕_k`-measurable). -/
def AdaptedM (S : MeasExpectationSystem Ω) (g : ℕ → Ω → ℝ) : Prop :=
  ∀ k, StronglyMeasurable[S.𝓕 k] (g k)

/-- **Woodford (2003), p. 593, on a filtered probability space**: `(π, x, i)` is an essentially
bounded adapted solution of the rule system — (2.6) and (3.1) at dates `≥ 2` and the rule (3.16)
at every date `n = t + 2`, a.s. — with history `π₁ = p₁`, `x₁ = x₁`, `i₁ = i₁`, `i₀ = i₀`. -/
def RuleSolM (S : MeasExpectationSystem Ω) (c : IRuleBasic.Calib) (γ : ℝ) (u rn : ℕ → Ω → ℝ)
    (p1 x1 i1 i0 : Ω → ℝ) (π x i : ℕ → Ω → ℝ) : Prop :=
  AdaptedM S π ∧ AdaptedM S x ∧ AdaptedM S i ∧ BndM S π ∧ BndM S x ∧ BndM S i ∧
    (∀ k, 2 ≤ k → ASm S c.β γ c.κ u π x k) ∧ (∀ k, 2 ≤ k → ISm S c.σ rn π x i k) ∧
    (∀ t, EulerM S c.β γ c.κ c.σ (fun k ω => i k ω - c.istar)
      (fbigM S c.β γ c.κ c.σ c.lx c.li π x) t) ∧
    π 1 = p1 ∧ x 1 = x1 ∧ i 1 = i1 ∧ i 0 = i0

/-- Woodford (2003), p. 593: the history `(π₁, x₁, i₁, i₀)` is essentially bounded, with
`π₁, x₁, i₁` known at date 1 and `i₀` at date 0. -/
def HistoryM (S : MeasExpectationSystem Ω) (p1 x1 i1 i0 : Ω → ℝ) : Prop :=
  StronglyMeasurable[S.𝓕 1] p1 ∧ StronglyMeasurable[S.𝓕 1] x1 ∧
    StronglyMeasurable[S.𝓕 1] i1 ∧ StronglyMeasurable[S.𝓕 0] i0 ∧
    ∃ K, ∀ᵐ ω ∂S.μ, |p1 ω| ≤ K ∧ |x1 ω| ≤ K ∧ |i1 ω| ≤ K ∧ |i0 ω| ≤ K

/-! ### Tools -/

/-- Woodford (2003), p. 593 (tool): the filtration shifted by two dates (the rule system starts
at `n = 2`). -/
def shift2 (S : MeasExpectationSystem Ω) : MeasExpectationSystem Ω where
  P := S.P
  𝓕 := ⟨fun s => S.𝓕 (s + 2), fun _ _ h => S.𝓕.mono (by omega), fun _ => S.𝓕.le _⟩

/-- Woodford (2003), p. 593 (tool): `E_s` of the shifted system is `E_{s+2}`. -/
theorem shift2_E (S : MeasExpectationSystem Ω) (s : ℕ) (x : Ω → ℝ) :
    (shift2 S).E s x = S.E (s + 2) x := rfl

/-- Woodford (2003), p. 540 (tool): `E_t(af + bg + c) = aE_tf + bg + c` a.s. for integrable `f`
and `g` known at `t`. -/
theorem E_lin_known (S : MeasExpectationSystem Ω) (t : ℕ) (a b c : ℝ) {f g : Ω → ℝ}
    (hf : Integrable f S.μ) (hgm : StronglyMeasurable[S.𝓕 t] g) (hg : Integrable g S.μ) :
    ∀ᵐ ω ∂S.μ, S.E t (fun ω => a * f ω + b * g ω + c) ω = a * S.E t f ω + b * g ω + c := by
  have e : (fun ω => a * f ω + b * g ω + c) = a • f + b • g + fun _ => c := by
    funext ω
    simp [smul_eq_mul]
  have hag : Integrable (a • f) S.μ := hf.smul a
  have hbg : Integrable (b • g) S.μ := hg.smul b
  rw [e]
  filter_upwards [S.E_add (hag.add hbg) (integrable_const c) t, S.E_add hag hbg t,
    S.E_smul a f t, S.E_smul b g t] with ω e1 e2 e3 e4
  rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, e4, S.E_const,
    S.E_of_stronglyMeasurable hgm hg]
  simp [smul_eq_mul]

/-- Woodford (2003), p. 540 (tool): `E_t(a₁f₁ + a₂f₂ + a₃f₃ + a₄f₄) = ∑ aⱼE_tfⱼ` a.s. for
integrable `fⱼ`. -/
theorem E_lin4 (S : MeasExpectationSystem Ω) (t : ℕ) (a1 a2 a3 a4 : ℝ) {f1 f2 f3 f4 : Ω → ℝ}
    (h1 : Integrable f1 S.μ) (h2 : Integrable f2 S.μ) (h3 : Integrable f3 S.μ)
    (h4 : Integrable f4 S.μ) :
    ∀ᵐ ω ∂S.μ, S.E t (fun ω => a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω) ω =
      a1 * S.E t f1 ω + a2 * S.E t f2 ω + a3 * S.E t f3 ω + a4 * S.E t f4 ω := by
  have e : (fun ω => a1 * f1 ω + a2 * f2 ω + a3 * f3 ω + a4 * f4 ω) =
      a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 := by
    funext ω
    simp [smul_eq_mul]
  have i1 : Integrable (a1 • f1) S.μ := h1.smul a1
  have i2 : Integrable (a2 • f2) S.μ := h2.smul a2
  have i3 : Integrable (a3 • f3) S.μ := h3.smul a3
  have i4 : Integrable (a4 • f4) S.μ := h4.smul a4
  rw [e]
  filter_upwards [S.E_add ((i1.add i2).add i3) i4 t, S.E_add (i1.add i2) i3 t, S.E_add i1 i2 t,
    S.E_smul a1 f1 t, S.E_smul a2 f2 t, S.E_smul a3 f3 t, S.E_smul a4 f4 t]
    with ω e1 e2 e3 e4 e5 e6 e7
  rw [e1, Pi.add_apply, e2, Pi.add_apply, e3, Pi.add_apply, e4, e5, e6, e7]
  simp [smul_eq_mul]

/-- Woodford (2003), p. 540 (tool): a bounded variable known at `k` is integrable. -/
theorem integrable_of_sm (S : MeasExpectationSystem Ω) {k : ℕ} {f : Ω → ℝ}
    (hm : StronglyMeasurable[S.𝓕 k] f) {C : ℝ} (hb : ∀ᵐ ω ∂S.μ, |f ω| ≤ C) :
    Integrable f S.μ :=
  integrable_of_bound ((hm.mono (S.𝓕.le k)).aestronglyMeasurable) hb

/-! ### Uniqueness: the conditional forecasts solve the perfect-foresight system -/

/-- **Woodford (2003), p. 593, with conditional expectations (the uniqueness step)**: let
`(dπ, dx, di)` be an essentially bounded adapted solution of the homogeneous rule system. If it
vanishes a.s. at date `n − 1` (and di at `n − 2`), then at almost every outcome the
conditional forecasts `m ↦ E_n d_{n−2+m}` are a bounded solution of the perfect-foresight rule
system with zero history, hence zero (`InflationInertiaRules.rule_system_unique`), so `d_n = 0`
a.s. -/
theorem forecast_zero (S : MeasExpectationSystem Ω) {β γ κ σ lx li : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hli : 0 < li) (hlx : 0 ≤ lx)
    {dπ dx di : ℕ → Ω → ℝ} (hπa : AdaptedM S dπ) (hxa : AdaptedM S dx) (hia : AdaptedM S di)
    (hπb : BndM S dπ) (hxb : BndM S dx) (hib : BndM S di)
    (hAS : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, dπ k ω - γ * dπ (k - 1) ω =
      κ * dx k ω + β * S.E k (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') ω)
    (hIS : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, dx k ω =
      S.E k (dx (k + 1)) ω - σ * (di k ω - S.E k (dπ (k + 1)) ω))
    (hEu : ∀ t, ∀ᵐ ω ∂S.μ, S.E (t + 2) (ALi β γ κ σ di t) ω =
      -(qtil γ κ σ lx li dπ dx (t + 2) ω -
        β * γ * S.E (t + 2) (qtil γ κ σ lx li dπ dx (t + 3)) ω))
    {n : ℕ} (hn : 2 ≤ n) (h1 : dπ (n - 1) =ᵐ[S.μ] 0) (h1x : dx (n - 1) =ᵐ[S.μ] 0)
    (h1i : di (n - 1) =ᵐ[S.μ] 0) (h2i : di (n - 2) =ᵐ[S.μ] 0) :
    dπ n =ᵐ[S.μ] 0 ∧ dx n =ᵐ[S.μ] 0 ∧ di n =ᵐ[S.μ] 0 := by
  obtain ⟨Cπ, hCπ⟩ := hπb
  obtain ⟨Cx, hCx⟩ := hxb
  obtain ⟨Ci, hCi⟩ := hib
  have iπ : ∀ k, Integrable (dπ k) S.μ := fun k => integrable_of_sm S (hπa k) (hCπ k)
  have ix : ∀ k, Integrable (dx k) S.μ := fun k => integrable_of_sm S (hxa k) (hCx k)
  have ii : ∀ k, Integrable (di k) S.μ := fun k => integrable_of_sm S (hia k) (hCi k)
  -- the forecast paths
  set pπ : Ω → ℕ → Unit → ℝ := fun ω m _ => S.E n (dπ (n - 2 + m)) ω with hpπ
  set px : Ω → ℕ → Unit → ℝ := fun ω m _ => S.E n (dx (n - 2 + m)) ω with hpx
  set pi : Ω → ℕ → Unit → ℝ := fun ω m _ => S.E n (di (n - 2 + m)) ω with hpi
  -- (2.6) along the forecasts
  have hASf : ∀ m, 2 ≤ m → ∀ᵐ ω ∂S.μ, pπ ω m () - γ * pπ ω (m - 1) () =
      κ * px ω m () + β * (pπ ω (m + 1) () - γ * pπ ω m ()) := by
    intro m hm
    set k := n - 2 + m with hk
    have hk1 : n - 2 + (m - 1) = k - 1 := by omega
    have hk2 : n - 2 + (m + 1) = k + 1 := by omega
    have hle : n ≤ k := by omega
    have e1 := S.E_congr (hAS k (by omega)) n
    have hin : Integrable (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') S.μ :=
      (iπ (k + 1)).sub ((iπ k).const_mul γ)
    filter_upwards [e1, E_lin4 S n 1 (-γ) 0 0 (iπ k) (iπ (k - 1)) (iπ k) (iπ k),
      E_lin4 S n κ β 0 0 (ix k) (S.integrable_E k (fun ω' => dπ (k + 1) ω' - γ * dπ k ω'))
        (iπ k) (iπ k), S.E_tower hle (fun ω' => dπ (k + 1) ω' - γ * dπ k ω'),
      E_lin4 S n 1 (-γ) 0 0 (iπ (k + 1)) (iπ k) (iπ k) (iπ k)] with ω a1 a2 a3 a4 a5
    simp only [hpπ, hpx, hk1, hk2]
    have l1 : S.E n (fun ω => dπ k ω - γ * dπ (k - 1) ω) ω =
        S.E n (dπ k) ω - γ * S.E n (dπ (k - 1)) ω := by
      have e : (fun ω => dπ k ω - γ * dπ (k - 1) ω) =
          fun ω => 1 * dπ k ω + -γ * dπ (k - 1) ω + 0 * dπ k ω + 0 * dπ k ω := by
        funext ω
        ring
      rw [e, a2]
      ring
    have l2 : S.E n (fun ω => κ * dx k ω + β * S.E k (fun ω' => dπ (k + 1) ω' -
        γ * dπ k ω') ω) ω = κ * S.E n (dx k) ω + β * (S.E n (dπ (k + 1)) ω -
          γ * S.E n (dπ k) ω) := by
      have e : (fun ω => κ * dx k ω + β * S.E k (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') ω) =
          fun ω => κ * dx k ω + β * S.E k (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') ω +
            0 * dπ k ω + 0 * dπ k ω := by
        funext ω
        ring
      have e5 : S.E n (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') ω =
          S.E n (dπ (k + 1)) ω - γ * S.E n (dπ k) ω := by
        have e : (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') =
            fun ω => 1 * dπ (k + 1) ω + -γ * dπ k ω + 0 * dπ k ω + 0 * dπ k ω := by
          funext ω
          ring
        rw [e, a5]
        ring
      rw [e, a3]
      have : S.E n (S.E k fun ω' => dπ (k + 1) ω' - γ * dπ k ω') ω =
          S.E n (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') ω := a4
      rw [this, e5]
      ring
    rw [← l1, ← l2]
    exact a1
  -- (3.1) along the forecasts
  have hISf : ∀ m, 2 ≤ m → ∀ᵐ ω ∂S.μ, px ω m () =
      px ω (m + 1) () - σ * (pi ω m () - pπ ω (m + 1) () - 0) := by
    intro m hm
    set k := n - 2 + m with hk
    have hk2 : n - 2 + (m + 1) = k + 1 := by omega
    have hle : n ≤ k := by omega
    have e1 := S.E_congr (hIS k (by omega)) n
    filter_upwards [e1, E_lin4 S n 1 (-σ) σ 0 (S.integrable_E k (dx (k + 1))) (ii k)
      (S.integrable_E k (dπ (k + 1))) (ii k), S.E_tower hle (dx (k + 1)),
      S.E_tower hle (dπ (k + 1))] with ω a1 a2 a3 a4
    simp only [hpπ, hpx, hpi, hk2]
    have e : (fun ω => S.E k (dx (k + 1)) ω - σ * (di k ω - S.E k (dπ (k + 1)) ω)) =
        fun ω => 1 * S.E k (dx (k + 1)) ω + -σ * di k ω + σ * S.E k (dπ (k + 1)) ω +
          0 * di k ω := by
      funext ω
      ring
    rw [a1, e, a2]
    have h3 : S.E n (S.E k (dx (k + 1))) ω = S.E n (dx (k + 1)) ω := a3
    have h4 : S.E n (S.E k (dπ (k + 1))) ω = S.E n (dπ (k + 1)) ω := a4
    rw [h3, h4]
    ring
  -- the qtil forecasts
  have hq : ∀ k, 1 ≤ k → ∀ᵐ ω ∂S.μ, S.E n (qtil γ κ σ lx li dπ dx k) ω =
      κ * σ / li * ((S.E n (dπ k) ω - γ * S.E n (dπ (k - 1)) ω) +
        lx / κ * (S.E n (dx k) ω - S.E n (dx (k - 1)) ω)) := by
    intro k _
    have e : qtil γ κ σ lx li dπ dx k = fun ω => (κ * σ / li) * dπ k ω +
        (-(κ * σ / li * γ)) * dπ (k - 1) ω + (κ * σ / li * (lx / κ)) * dx k ω +
          (-(κ * σ / li * (lx / κ))) * dx (k - 1) ω := by
      funext ω
      simp only [qtil]
      ring
    filter_upwards [E_lin4 S n (κ * σ / li) (-(κ * σ / li * γ)) (κ * σ / li * (lx / κ))
      (-(κ * σ / li * (lx / κ))) (iπ k) (iπ (k - 1)) (ix k) (ix (k - 1))] with ω a
    rw [e, a]
    ring
  -- (3.16) along the forecasts
  have hEuf : ∀ t', ∀ᵐ ω ∂S.μ, InflationInertiaRules.ALi β γ κ σ
      (fun k u => pi ω k u - 0) t' () =
      -(qtil γ κ σ lx li (pπ ω) (px ω) (t' + 2) () -
        β * γ * qtil γ κ σ lx li (pπ ω) (px ω) (t' + 2 + 1) ()) := by
    intro t'
    set t := n - 2 + t' with ht
    have hle : n ≤ t + 2 := by omega
    have e1 := S.E_congr (hEu t) n
    have hqi : ∀ k, Integrable (qtil γ κ σ lx li dπ dx k) S.μ := by
      intro k
      have e : qtil γ κ σ lx li dπ dx k = fun ω => (κ * σ / li) * dπ k ω +
          (-(κ * σ / li * γ)) * dπ (k - 1) ω + (κ * σ / li * (lx / κ)) * dx k ω +
            (-(κ * σ / li * (lx / κ))) * dx (k - 1) ω := by
        funext ω
        simp only [qtil]
        ring
      rw [e]
      exact ((((iπ k).const_mul _).add ((iπ (k - 1)).const_mul _)).add
        ((ix k).const_mul _)).add ((ix (k - 1)).const_mul _)
    have hALi : InflationInertiaRules.ALi β γ κ σ di t = fun ω => (β * γ) * di (t + 3) ω +
        (-(1 + γ + β * γ)) * di (t + 2) ω + CubicRoots.coefA2 β γ κ σ * di (t + 1) ω + (-β⁻¹) * di
            t ω := by
      funext ω
      simp only [InflationInertiaRules.ALi]
      ring
    filter_upwards [e1, S.E_tower hle (InflationInertiaRules.ALi β γ κ σ di t),
      E_lin4 S n (β * γ) (-(1 + γ + β * γ)) (CubicRoots.coefA2 β γ κ σ) (-β⁻¹) (ii (t + 3)) (ii (t
          + 2))
        (ii (t + 1)) (ii t),
      E_lin4 S n (-1) (β * γ) 0 0 (hqi (t + 2)) (S.integrable_E (t + 2) (qtil γ κ σ lx li dπ dx
        (t + 3))) (hqi 0) (hqi 0),
      S.E_tower hle (qtil γ κ σ lx li dπ dx (t + 3)), hq (t + 2) (by omega),
      hq (t + 3) (by omega)] with ω a1 a2 a3 a4 a5 a6 a7
    have lhs : S.E n (S.E (t + 2) (InflationInertiaRules.ALi β γ κ σ di t)) ω =
        (β * γ) * S.E n (di (t + 3)) ω + (-(1 + γ + β * γ)) * S.E n (di (t + 2)) ω +
          CubicRoots.coefA2 β γ κ σ * S.E n (di (t + 1)) ω + (-β⁻¹) * S.E n (di t) ω := by
      rw [a2, hALi, a3]
    have rhs : S.E n (fun ω => -(qtil γ κ σ lx li dπ dx (t + 2) ω -
        β * γ * S.E (t + 2) (qtil γ κ σ lx li dπ dx (t + 3)) ω)) ω =
        -(S.E n (qtil γ κ σ lx li dπ dx (t + 2)) ω -
          β * γ * S.E n (qtil γ κ σ lx li dπ dx (t + 3)) ω) := by
      have e : (fun ω => -(qtil γ κ σ lx li dπ dx (t + 2) ω -
          β * γ * S.E (t + 2) (qtil γ κ σ lx li dπ dx (t + 3)) ω)) = fun ω =>
          (-1) * qtil γ κ σ lx li dπ dx (t + 2) ω +
            (β * γ) * S.E (t + 2) (qtil γ κ σ lx li dπ dx (t + 3)) ω +
            0 * qtil γ κ σ lx li dπ dx 0 ω + 0 * qtil γ κ σ lx li dπ dx 0 ω := by
        funext ω
        ring
      rw [e, a4]
      have : S.E n (S.E (t + 2) (qtil γ κ σ lx li dπ dx (t + 3))) ω =
          S.E n (qtil γ κ σ lx li dπ dx (t + 3)) ω := a5
      rw [this]
      ring
    have hfin := lhs.symm.trans (a1.trans rhs)
    rw [a6, a7] at hfin
    simp only [InflationInertiaRules.ALi, qtil, hpπ, hpx, hpi, sub_zero]
    have i1 : n - 2 + (t' + 3) = t + 3 := by omega
    have i2 : n - 2 + (t' + 2) = t + 2 := by omega
    have i3 : n - 2 + (t' + 1) = t + 1 := by omega
    have i5 : n - 2 + (t' + 2 + 1 - 1) = t + 2 := by omega
    have i6 : n - 2 + (t' + 2 - 1) = t + 1 := by omega
    have i7 : t + 3 - 1 = t + 2 := by omega
    have i8 : t + 2 - 1 = t + 1 := by omega
    rw [i7, i8] at hfin
    rw [i1, i2, i3, ← ht, i6, i5]
    linear_combination hfin
  -- bounds and the zero history of the forecasts
  have hbd : ∀ᵐ ω ∂S.μ, ∀ m, |pπ ω m ()| ≤ Cπ ∧ |px ω m ()| ≤ Cx ∧ |pi ω m ()| ≤ Ci := by
    refine ae_all_iff.2 fun m => ?_
    filter_upwards [S.abs_E_le (hCπ (n - 2 + m)) n, S.abs_E_le (hCx (n - 2 + m)) n,
      S.abs_E_le (hCi (n - 2 + m)) n] with ω a b c
    exact ⟨a, b, c⟩
  have hh : ∀ᵐ ω ∂S.μ, pπ ω 1 () = 0 ∧ px ω 1 () = 0 ∧ pi ω 1 () = 0 ∧ pi ω 0 () = 0 := by
    filter_upwards [S.E_congr h1 n, S.E_congr h1x n, S.E_congr h1i n, S.E_congr h2i n]
      with ω a b c d
    simp only [hpπ, hpx, hpi, show n - 2 + 1 = n - 1 by omega, add_zero]
    rw [a, b, c, d, S.E_zero]
    exact ⟨rfl, rfl, rfl, rfl⟩
  have hASa : ∀ᵐ ω ∂S.μ, ∀ m, 2 ≤ m → pπ ω m () - γ * pπ ω (m - 1) () =
      κ * px ω m () + β * (pπ ω (m + 1) () - γ * pπ ω m ()) := by
    refine ae_all_iff.2 fun m => ?_
    by_cases hm : 2 ≤ m
    · exact (hASf m hm).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hm
  have hISa : ∀ᵐ ω ∂S.μ, ∀ m, 2 ≤ m → px ω m () =
      px ω (m + 1) () - σ * (pi ω m () - pπ ω (m + 1) () - 0) := by
    refine ae_all_iff.2 fun m => ?_
    by_cases hm : 2 ≤ m
    · exact (hISf m hm).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hm
  have hda := fun k => S.E_of_stronglyMeasurable (hπa k) (iπ k)
  have hdx := fun k => S.E_of_stronglyMeasurable (hxa k) (ix k)
  have hdi := fun k => S.E_of_stronglyMeasurable (hia k) (ii k)
  have hfinal : ∀ᵐ ω ∂S.μ, dπ n ω = 0 ∧ dx n ω = 0 ∧ di n ω = 0 := by
    filter_upwards [hASa, hISa, ae_all_iff.2 hEuf, hbd, hh] with ω eAS eIS eEu eb eh
    have b0 : InflationInertiaRules.Bnd (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) :=
      ⟨0, le_rfl, fun _ _ => by simp⟩
    have key := InflationInertiaRules.rule_system_unique perfectForesight
      perfectForesight_pullOut ExpectationTools.perfectForesight_faithful (lamx := lx)
      (lami := li) (istar := 0) hβ0 hβ1 hκ hσ hli hlx (u := fun _ _ => 0)
      (rn := fun _ _ => 0) (π := pπ ω) (x := px ω) (i := pi ω) (π' := fun _ _ => 0)
      (x' := fun _ _ => 0) (i' := fun _ _ => 0) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      ⟨max Cπ 0, le_max_right _ _, fun k _ => (eb k).1.trans (le_max_left _ _)⟩
      ⟨max Cx 0, le_max_right _ _, fun k _ => (eb k).2.1.trans (le_max_left _ _)⟩
      ⟨max Ci 0, le_max_right _ _, fun k _ => (eb k).2.2.trans (le_max_left _ _)⟩ b0 b0 b0
      (fun k hk _ => by
        change pπ ω k () - γ * pπ ω (k - 1) () =
          κ * px ω k () + β * (pπ ω (k + 1) () - γ * pπ ω k ()) + 0
        rw [add_zero]
        exact eAS k hk)
      (fun k _ _ => by
        change (0 : ℝ) - γ * 0 = κ * 0 + β * (0 - γ * 0) + 0
        ring)
      (fun k hk _ => eIS k hk)
      (fun k _ _ => by
        change (0 : ℝ) = 0 - σ * (0 - 0 - 0)
        ring)
      (fun t _ => eEu t)
      (fun t _ => by
        change ALi β γ κ σ (fun k ω => (fun _ _ => (0 : ℝ)) k ω - 0) t () =
          -(qtil γ κ σ lx li (fun _ _ => 0) (fun _ _ => 0) (t + 2) () -
            β * γ * qtil γ κ σ lx li (fun _ _ => 0) (fun _ _ => 0) (t + 2 + 1) ())
        simp [ALi, qtil])
      (fun _ => eh.1) (fun _ => eh.2.1) (fun _ => eh.2.2.1) (fun _ => eh.2.2.2)
    obtain ⟨k1, k2, k3⟩ := key 2 (by norm_num) ()
    simp only [hpπ, hpx, hpi, show n - 2 + 2 = n by omega] at k1 k2 k3
    rw [hda n] at k1
    rw [hdx n] at k2
    rw [hdi n] at k3
    exact ⟨k1, k2, k3⟩
  exact ⟨hfinal.mono fun ω h => h.1, hfinal.mono fun ω h => h.2.1,
    hfinal.mono fun ω h => h.2.2⟩

/-- **Woodford (2003), p. 593, on a filtered probability space: the rule system has at most one
solution.** For every admissible calibration (`0 < β < 1`, `κ, σ ≠ 0`, `λᵢ > 0`, `λₓ ≥ 0`), every
`γ`, two essentially bounded adapted solutions with the same disturbances and history agree a.s.
at every date `≥ 1` (by induction, with `forecast_zero` at each date). -/
theorem rule_system_uniqueM (S : MeasExpectationSystem Ω) (c : IRuleBasic.Calib) {γ : ℝ}
    (hβ0 : 0 < c.β) (hβ1 : c.β < 1) (hκ : c.κ ≠ 0) (hσ : c.σ ≠ 0) (hli : 0 < c.li)
    (hlx : 0 ≤ c.lx) {u rn : ℕ → Ω → ℝ} {p1 x1 i1 i0 : Ω → ℝ} {π x i π' x' i' : ℕ → Ω → ℝ}
    (h : RuleSolM S c γ u rn p1 x1 i1 i0 π x i) (h' : RuleSolM S c γ u rn p1 x1 i1 i0 π' x' i') :
    ∀ k, 1 ≤ k → π k =ᵐ[S.μ] π' k ∧ x k =ᵐ[S.μ] x' k ∧ i k =ᵐ[S.μ] i' k := by
  obtain ⟨hπa, hxa, hia, ⟨Cπ, hCπ⟩, ⟨Cx, hCx⟩, ⟨Ci, hCi⟩, hAS, hIS, hEu, h1π, h1x, h1i, h0i⟩ := h
  obtain ⟨hπa', hxa', hia', ⟨Cπ', hCπ'⟩, ⟨Cx', hCx'⟩, ⟨Ci', hCi'⟩, hAS', hIS', hEu', h1π', h1x',
    h1i', h0i'⟩ := h'
  have iπ : ∀ k, Integrable (π k) S.μ := fun k => integrable_of_sm S (hπa k) (hCπ k)
  have ix : ∀ k, Integrable (x k) S.μ := fun k => integrable_of_sm S (hxa k) (hCx k)
  have ii : ∀ k, Integrable (i k) S.μ := fun k => integrable_of_sm S (hia k) (hCi k)
  have iπ' : ∀ k, Integrable (π' k) S.μ := fun k => integrable_of_sm S (hπa' k) (hCπ' k)
  have ix' : ∀ k, Integrable (x' k) S.μ := fun k => integrable_of_sm S (hxa' k) (hCx' k)
  have ii' : ∀ k, Integrable (i' k) S.μ := fun k => integrable_of_sm S (hia' k) (hCi' k)
  set dπ : ℕ → Ω → ℝ := fun k ω => π k ω - π' k ω with hdπ
  set dx : ℕ → Ω → ℝ := fun k ω => x k ω - x' k ω with hdx
  set di : ℕ → Ω → ℝ := fun k ω => i k ω - i' k ω with hdi
  have iA : ∀ (j : ℕ → Ω → ℝ), (∀ k, Integrable (j k) S.μ) → ∀ t,
      Integrable (ALi c.β γ c.κ c.σ j t) S.μ := fun j hj t =>
    ((((hj (t + 3)).const_mul (c.β * γ)).sub ((hj (t + 2)).const_mul (1 + γ + c.β * γ))).add
      ((hj (t + 1)).const_mul (CubicRoots.coefA2 c.β γ c.κ c.σ))).sub ((hj t).const_mul c.β⁻¹)
  have iQ : ∀ (p q : ℕ → Ω → ℝ), (∀ k, Integrable (p k) S.μ) → (∀ k, Integrable (q k) S.μ) →
      ∀ k, Integrable (qtil γ c.κ c.σ c.lx c.li p q k) S.μ := fun p q hp hq k =>
    (((hp k).sub ((hp (k - 1)).const_mul γ)).add
      (((hq k).sub (hq (k - 1))).const_mul (c.lx / c.κ))).const_mul (c.κ * c.σ / c.li)
  have iı : ∀ k, Integrable (fun ω => i k ω - c.istar) S.μ := fun k =>
    (ii k).sub (integrable_const _)
  have iı' : ∀ k, Integrable (fun ω => i' k ω - c.istar) S.μ := fun k =>
    (ii' k).sub (integrable_const _)
  -- the homogeneous system for the differences
  have hASd : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, dπ k ω - γ * dπ (k - 1) ω =
      c.κ * dx k ω + c.β * S.E k (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') ω := by
    intro k hk
    have i1 : Integrable (fun ω' => π (k + 1) ω' - γ * π k ω') S.μ :=
      (iπ (k + 1)).sub ((iπ k).const_mul γ)
    have i2 : Integrable (fun ω' => π' (k + 1) ω' - γ * π' k ω') S.μ :=
      (iπ' (k + 1)).sub ((iπ' k).const_mul γ)
    have e : (fun ω' => dπ (k + 1) ω' - γ * dπ k ω') =
        (fun ω' => π (k + 1) ω' - γ * π k ω') - fun ω' => π' (k + 1) ω' - γ * π' k ω' := by
      funext ω'
      simp only [hdπ, Pi.sub_apply]
      ring
    filter_upwards [hAS k hk, hAS' k hk, S.E_sub i1 i2 k] with ω a a' e2
    rw [e, e2, Pi.sub_apply]
    simp only [hdπ, hdx]
    linear_combination a - a'
  have hISd : ∀ k, 2 ≤ k → ∀ᵐ ω ∂S.μ, dx k ω =
      S.E k (dx (k + 1)) ω - c.σ * (di k ω - S.E k (dπ (k + 1)) ω) := by
    intro k hk
    filter_upwards [hIS k hk, hIS' k hk, S.E_sub (ix (k + 1)) (ix' (k + 1)) k,
      S.E_sub (iπ (k + 1)) (iπ' (k + 1)) k] with ω a a' e1 e2
    have f1 : S.E k (dx (k + 1)) ω = S.E k (x (k + 1)) ω - S.E k (x' (k + 1)) ω := e1
    have f2 : S.E k (dπ (k + 1)) ω = S.E k (π (k + 1)) ω - S.E k (π' (k + 1)) ω := e2
    rw [f1, f2]
    simp only [hdx, hdi]
    linear_combination a - a'
  have hEud : ∀ t, ∀ᵐ ω ∂S.μ, S.E (t + 2) (ALi c.β γ c.κ c.σ di t) ω =
      -(qtil γ c.κ c.σ c.lx c.li dπ dx (t + 2) ω -
        c.β * γ * S.E (t + 2) (qtil γ c.κ c.σ c.lx c.li dπ dx (t + 3)) ω) := by
    intro t
    have eA : ALi c.β γ c.κ c.σ di t = ALi c.β γ c.κ c.σ (fun k ω => i k ω - c.istar) t -
        ALi c.β γ c.κ c.σ (fun k ω => i' k ω - c.istar) t := by
      funext ω
      simp only [ALi, hdi, Pi.sub_apply]
      ring
    have eQ : ∀ k, qtil γ c.κ c.σ c.lx c.li dπ dx k =
        qtil γ c.κ c.σ c.lx c.li π x k - qtil γ c.κ c.σ c.lx c.li π' x' k := by
      intro k
      funext ω
      simp only [qtil, hdπ, hdx, Pi.sub_apply]
      ring
    filter_upwards [hEu t, hEu' t, S.E_sub (iA _ iı t) (iA _ iı' t) (t + 2),
      S.E_sub (iQ π x iπ ix (t + 3)) (iQ π' x' iπ' ix' (t + 3)) (t + 2)] with ω a a' e1 e2
    rw [eA, e1, Pi.sub_apply, eQ (t + 3), e2, Pi.sub_apply, eQ (t + 2), Pi.sub_apply]
    simp only [fbigM] at a a'
    rw [show t + 2 + 1 = t + 3 by omega] at a a'
    linear_combination a - a'
  have hda : AdaptedM S dπ := fun k => (hπa k).sub (hπa' k)
  have hdxa : AdaptedM S dx := fun k => (hxa k).sub (hxa' k)
  have hdia : AdaptedM S di := fun k => (hia k).sub (hia' k)
  have hdb : ∀ {p p' : ℕ → Ω → ℝ} {C C' : ℝ}, (∀ k, ∀ᵐ ω ∂S.μ, |p k ω| ≤ C) →
      (∀ k, ∀ᵐ ω ∂S.μ, |p' k ω| ≤ C') → BndM S (fun k ω => p k ω - p' k ω) :=
    fun {_ _ C C'} hp hp' => ⟨C + C', fun k => (hp k).mp ((hp' k).mono fun ω h1 h2 =>
      (abs_sub _ _).trans (add_le_add h2 h1))⟩
  have hz : ∀ m, (dπ (m + 1) =ᵐ[S.μ] 0 ∧ dx (m + 1) =ᵐ[S.μ] 0 ∧ di (m + 1) =ᵐ[S.μ] 0) ∧
      di m =ᵐ[S.μ] 0 := by
    intro m
    induction m with
    | zero =>
      refine ⟨⟨ae_of_all _ fun ω => ?_, ae_of_all _ fun ω => ?_, ae_of_all _ fun ω => ?_⟩,
        ae_of_all _ fun ω => ?_⟩
      · simp [hdπ, h1π, h1π']
      · simp [hdx, h1x, h1x']
      · simp [hdi, h1i, h1i']
      · simp [hdi, h0i, h0i']
    | succ m ih =>
      obtain ⟨⟨a1, a2, a3⟩, a4⟩ := ih
      have key := forecast_zero S hβ0 hβ1 hκ hσ hli hlx hda hdxa hdia (hdb hCπ hCπ')
        (hdb hCx hCx') (hdb hCi hCi') hASd hISd hEud (n := m + 1 + 1) (by omega)
        (by rwa [show m + 1 + 1 - 1 = m + 1 by omega]) (by rwa [show m + 1 + 1 - 1 = m + 1 by
            omega])
        (by rwa [show m + 1 + 1 - 1 = m + 1 by omega]) (by rwa [show m + 1 + 1 - 2 = m by omega])
      exact ⟨key, a3⟩
  intro k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨⟨a1, a2, a3⟩, -⟩ := hz m
  exact ⟨a1.mono fun ω h => sub_eq_zero.mp h, a2.mono fun ω h => sub_eq_zero.mp h,
    a3.mono fun ω h => sub_eq_zero.mp h⟩

/-! ### Existence for `0 < γ ≤ 1` -/

namespace PosM

open TidyR5aLambdaXZero.Pos (Abk Pinv Pm A1 A2 MXZ MXX Fvec wPos x0vec c0)

variable {β γ κ σ li : ℝ}

/-- Woodford (2003), p. 593: inflation from a path (`π_0 = 0`, `π_1 = p₁`,
`π_{s+2} = Y_s`). -/
def πM (p1 : Ω → ℝ) (Y : ℕ → Ω → Fin 3 ⊕ Fin 3 → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => p1
  | s + 2 => fun ω => Y s ω (Sum.inl 0)

/-- Woodford (2003), p. 593: the output gap from a path (`x_0 = 0`, `x_1 = x₁`). -/
def xM (x1 : Ω → ℝ) (Y : ℕ → Ω → Fin 3 ⊕ Fin 3 → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => x1
  | s + 2 => fun ω => Y s ω (Sum.inl 1)

/-- Woodford (2003), p. 593: the interest rate from a path (`i_0 = i₀`, `i_1 = i₁`,
`i_{s+2} = i* + ı_{s+2}`). -/
def iM (istar : ℝ) (i1 i0 : Ω → ℝ) (Y : ℕ → Ω → Fin 3 ⊕ Fin 3 → ℝ) : ℕ → Ω → ℝ
  | 0 => i0
  | 1 => i1
  | s + 2 => fun ω => Y s ω (Sum.inl 2) + istar

variable (β γ κ σ li) in
/-- Woodford (2003), App. C.1 (tool): the forcing of the Blanchard–Kahn form, random vector
ordering. -/
noncomputable def wM (u rn : ℕ → Ω → ℝ) (istar : ℝ) : ℕ → Ω → Fin 3 ⊕ Fin 3 → ℝ :=
  fun s ω k => wPos β γ κ σ li u rn istar s k ω

/-- Woodford (2003), p. 593: the initial predetermined state `(π₁, ı₁, ı₀)`, random vector
ordering. -/
def x0M (p1 i1 i0 : Ω → ℝ) (istar : ℝ) : Ω → Fin 3 → ℝ :=
  fun ω j => x0vec p1 i1 i0 istar j ω

/-- Woodford (2003), p. 593 (tool), with conditional expectations: along an equilibrium the
predetermined block is a.s. the lagged `(π_{n−1}, ı_{n−1}, ı_{n−2})`. -/
theorem lagsM {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ}
    {p1 i1 i0 : Ω → ℝ} {Y : ℕ → Ω → Fin 3 ⊕ Fin 3 → ℝ}
    (hY : MEquil (shift2 S) (Abk β γ κ σ li) (wM β γ κ σ li u rn istar)
      (x0M p1 i1 i0 istar) Y) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, Y s ω (Sum.inr 0) = πM p1 Y (s + 1) ω ∧
      Y s ω (Sum.inr 1) = iM istar i1 i0 Y (s + 1) ω - istar ∧
      Y s ω (Sum.inr 2) = iM istar i1 i0 Y s ω - istar := by
  obtain ⟨hS, ha, hpk, h0, hb⟩ := hY
  have hi := integrable_of_adapted hb ha
  induction s with
  | zero =>
    filter_upwards [h0] with ω e
    refine ⟨?_, ?_, ?_⟩
    · rw [e 0]
      rfl
    · rw [e 1]
      rfl
    · rw [e 2]
      rfl
  | succ s ih =>
    have key : ∀ᵐ ω ∂S.μ, ∀ j, Y (s + 1) ω (Sum.inr j) =
        (MXZ *ᵥ fun i => Y s ω (Sum.inl i)) j + (MXX *ᵥ fun i => Y s ω (Sum.inr i)) j := by
      filter_upwards [hS s] with ω e j
      have hk : (shift2 S).E s (fun ω' => Y (s + 1) ω' (Sum.inr j)) ω = Y (s + 1) ω (Sum.inr j) :=
        congrFun ((shift2 S).E_of_stronglyMeasurable (hpk s j) (hi (s + 1) (Sum.inr j))) ω
      have e2 := congrFun e (Sum.inr j)
      change (shift2 S).E s (fun ω' => Y (s + 1) ω' (Sum.inr j)) ω = _ at e2
      rw [hk] at e2
      rw [e2]
      have hv : Y s ω = Sum.elim (fun i => Y s ω (Sum.inl i)) (fun i => Y s ω (Sum.inr i)) := by
        funext k
        rcases k with i | i <;> rfl
      rw [hv, Abk, fromBlocks_mulVec]
      simp [wM, wPos]
    filter_upwards [key, ih] with ω e ih
    refine ⟨?_, ?_, ?_⟩
    · rw [e 0]
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_three, πM]
    · rw [e 1]
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_three, iM]
    · rw [e 2]
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_three, ih.2.1]

/-- Woodford (2003), (2.6), (3.1), (3.16) at `λₓ = 0`, date `n = s + 2`, a.s., from an
equilibrium: `P E_n(π, x, ı)_{n+1} = A₁(π, x, ı)_n + A₂(π_{n−1}, ı_{n−1}, ı_{n−2}) + F_n`. -/
theorem rowsM (hβ : β ≠ 0) (hγ : γ ≠ 0) {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ}
    {istar : ℝ} {x0 : Ω → Fin 3 → ℝ} {Y : ℕ → Ω → Fin 3 ⊕ Fin 3 → ℝ}
    (hY : MEquil (shift2 S) (Abk β γ κ σ li) (wM β γ κ σ li u rn istar) x0 Y) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, Pm β γ κ σ li *ᵥ (fun j => S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl j)) ω) =
      A1 β γ κ σ li *ᵥ (fun j => Y s ω (Sum.inl j)) + A2 β γ κ σ li *ᵥ
        (fun j => Y s ω (Sum.inr j)) + Fvec σ u rn istar s ω := by
  filter_upwards [hY.1 s] with ω e
  have hv : Y s ω = Sum.elim (fun i => Y s ω (Sum.inl i)) (fun i => Y s ω (Sum.inr i)) := by
    funext k
    rcases k with i | i <;> rfl
  have hE : (fun j => S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl j)) ω) =
      Pinv β γ κ σ li *ᵥ (A1 β γ κ σ li *ᵥ (fun j => Y s ω (Sum.inl j)) + A2 β γ κ σ li *ᵥ
        (fun j => Y s ω (Sum.inr j)) + Fvec σ u rn istar s ω) := by
    funext j
    have := congrFun e (Sum.inl j)
    change S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl j)) ω = _ at this
    rw [this, hv, Abk, fromBlocks_mulVec]
    simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, wM, wPos,
      ← mulVec_mulVec, mulVec_add]
    rfl
  rw [hE, mulVec_mulVec, TidyR5aLambdaXZero.Pos.Pm_mul_Pinv β γ κ σ li hβ hγ, one_mulVec]

/-- **Woodford (2003), (2.6), (3.1), (3.16) at `λₓ = 0`, with conditional expectations, from an
equilibrium** (dates from `n = 2`): the plan `(πM, xM, iM)` satisfies (2.6) and (3.1) a.s. at
every date `≥ 2` and the rule (3.16) a.s. at every date `n = t + 2`. -/
theorem eqsM (hβ : β ≠ 0) (hγ : γ ≠ 0) {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ}
    {istar : ℝ} {p1 x1 i1 i0 : Ω → ℝ} {Y : ℕ → Ω → Fin 3 ⊕ Fin 3 → ℝ}
    (hY : MEquil (shift2 S) (Abk β γ κ σ li) (wM β γ κ σ li u rn istar)
      (x0M p1 i1 i0 istar) Y) :
    (∀ k, 2 ≤ k → ASm S β γ κ u (πM p1 Y) (xM x1 Y) k) ∧
      (∀ k, 2 ≤ k → ISm S σ rn (πM p1 Y) (xM x1 Y) (iM istar i1 i0 Y) k) ∧
      ∀ t, EulerM S β γ κ σ (fun k ω => iM istar i1 i0 Y k ω - istar)
        (fbigM S β γ κ σ 0 li (πM p1 Y) (xM x1 Y)) t := by
  have hl := lagsM hY
  have hr := rowsM hβ hγ hY
  obtain ⟨-, ha, -, -, hb⟩ := hY
  have hi : ∀ s k, Integrable (fun ω => Y s ω k) S.μ := fun s k =>
    integrable_of_adapted (S := shift2 S) hb ha s k
  have hm : ∀ s k, StronglyMeasurable[S.𝓕 (s + 2)] (fun ω => Y s ω k) := fun s k => ha s k
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun t => ?_⟩
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    have e1 : (fun ω' => πM p1 Y (s + 2 + 1) ω' - γ * πM p1 Y (s + 2) ω') =
        fun ω' => 1 * Y (s + 1) ω' (Sum.inl 0) + (-γ) * Y s ω' (Sum.inl 0) + 0 := by
      funext ω'
      simp only [πM]
      ring
    filter_upwards [hr s, hl s, E_lin_known S (s + 2) 1 (-γ) 0 (hi (s + 1) (Sum.inl 0))
      (hm s (Sum.inl 0)) (hi s (Sum.inl 0))] with ω r l e
    have r0 : β * S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 0)) ω =
        (1 + β * γ) * Y s ω (Sum.inl 0) + -(κ * Y s ω (Sum.inl 1)) +
          -(γ * Y s ω (Sum.inr 0)) + -u (s + 2) ω := by
      have h := congrFun r 0
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_three] at h
      linear_combination h
    rw [e1, e, show s + 2 - 1 = s + 1 by omega, ← l.1]
    simp only [πM, xM]
    linear_combination -r0
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    filter_upwards [hr s] with ω r
    have r1 : σ * S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 0)) ω +
        S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 1)) ω =
        Y s ω (Sum.inl 1) + σ * Y s ω (Sum.inl 2) + σ * (istar - rn (s + 2) ω) := by
      have h := congrFun r 1
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_three] at h
      linear_combination h
    change Y s ω (Sum.inl 1) = S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 1)) ω -
      σ * ((Y s ω (Sum.inl 2) + istar) - S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 0)) ω -
        rn (s + 2) ω)
    linear_combination -r1
  · have hALi : ∀ᵐ ω ∂S.μ, ALi β γ κ σ (fun k ω => iM istar i1 i0 Y k ω - istar) t ω =
        (β * γ) * Y (t + 1) ω (Sum.inl 2) + (-(1 + γ + β * γ)) * Y t ω (Sum.inl 2) +
          CubicRoots.coefA2 β γ κ σ * Y t ω (Sum.inr 1) + (-β⁻¹) * Y t ω (Sum.inr 2) := by
      filter_upwards [hl t] with ω l
      simp only [ALi]
      rw [← l.2.1, ← l.2.2]
      simp only [iM]
      ring
    have hq3 : qtil γ κ σ 0 li (πM p1 Y) (xM x1 Y) (t + 3) = fun ω =>
        (κ * σ / li) * Y (t + 1) ω (Sum.inl 0) + (-(κ * σ / li * γ)) * Y t ω (Sum.inl 0) + 0 := by
      funext ω
      simp only [qtil, πM, zero_div, zero_mul, add_zero, show t + 3 - 1 = t + 2 by omega]
      ring
    filter_upwards [hr t, hl t, S.E_congr hALi (t + 2),
      E_lin4 S (t + 2) (β * γ) (-(1 + γ + β * γ)) (CubicRoots.coefA2 β γ κ σ) (-β⁻¹)
        (hi (t + 1) (Sum.inl 2)) (hi t (Sum.inl 2)) (hi t (Sum.inr 1)) (hi t (Sum.inr 2)),
      E_lin_known S (t + 2) (κ * σ / li) (-(κ * σ / li * γ)) 0 (hi (t + 1) (Sum.inl 0))
        (hm t (Sum.inl 0)) (hi t (Sum.inl 0))] with ω r l eA e4 eq
    have r2 : -(β * γ * c0 κ σ li) * S.E (t + 2) (fun ω' => Y (t + 1) ω' (Sum.inl 0)) ω +
        β * γ * S.E (t + 2) (fun ω' => Y (t + 1) ω' (Sum.inl 2)) ω =
        -(c0 κ σ li * (1 + β * γ ^ 2)) * Y t ω (Sum.inl 0) + (1 + γ + β * γ) * Y t ω (Sum.inl 2) +
          c0 κ σ li * γ * Y t ω (Sum.inr 0) + -CubicRoots.coefA2 β γ κ σ * Y t ω (Sum.inr 1) +
          β⁻¹ * Y t ω (Sum.inr 2) := by
      have h := congrFun r 2
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_three] at h
      linear_combination h
    have k2 : S.E (t + 2) (fun ω => Y t ω (Sum.inl 2)) = fun ω => Y t ω (Sum.inl 2) :=
      S.E_of_stronglyMeasurable (hm t _) (hi t _)
    have k3 : S.E (t + 2) (fun ω => Y t ω (Sum.inr 1)) = fun ω => Y t ω (Sum.inr 1) :=
      S.E_of_stronglyMeasurable (hm t _) (hi t _)
    have k4 : S.E (t + 2) (fun ω => Y t ω (Sum.inr 2)) = fun ω => Y t ω (Sum.inr 2) :=
      S.E_of_stronglyMeasurable (hm t _) (hi t _)
    rw [eA, e4, k2, k3, k4]
    simp only [fbigM]
    rw [show t + 2 + 1 = t + 3 by omega, hq3, eq]
    have hq2 : qtil γ κ σ 0 li (πM p1 Y) (xM x1 Y) (t + 2) ω =
        κ * σ / li * (Y t ω (Sum.inl 0) - γ * Y t ω (Sum.inr 0)) := by
      simp only [qtil, zero_div, zero_mul, add_zero, show t + 2 - 1 = t + 1 by omega]
      rw [l.1]
      rfl
    rw [hq2]
    simp only [c0] at r2
    linear_combination r2

/-- **Woodford (2003), p. 593, on a filtered probability space: existence at `λₓ = 0` for
`0 < γ ≤ 1`.** For every essentially bounded adapted disturbance `(u, rⁿ)` and every essentially
bounded history (`π₁, x₁, i₁` known at 1, `i₀` at 0), the rule system (2.6), (3.1), (3.16) with
`λₓ = 0` has an essentially bounded adapted solution with that history: the equilibrium of the
Blanchard–Kahn matrix `TidyR5aLambdaXZero.Pos.Abk` from date 2 on
(`TidyR5aMeasBK.m_bk_exists`), with the history glued in. -/
theorem existsM (c : IRuleBasic.Calib) (hlx : c.lx = 0) (h : CubicRoots.Assumptions.Standing c.β γ
    c.κ c.σ)
    (hli : 0 < c.li) (S : MeasExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u)
    (hub : BndM S u) (hra : AdaptedM S rn) (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : HistoryM S p1 x1 i1 i0) : ∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i := by
  have hβ := h.beta_pos.ne'
  have hγ := h.gamma_pos.ne'
  obtain ⟨hnu, hcount⟩ := TidyR5aLambdaXZero.Pos.bk_roots c.β γ c.κ c.σ c.li h hli
  have hd : Module.finrank ℝ (boundedOrbits (Abk c.β γ c.κ c.σ c.li)) = Fintype.card (Fin 3) := by
    rw [BKInvariantSplit.finrank_eq_stableCount hnu, hcount, Fintype.card_fin]
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  obtain ⟨Cu, hCu⟩ := hub
  obtain ⟨Cr, hCr⟩ := hrb
  obtain ⟨Kw, hKw⟩ := GeneralFOC.exists_bound_mulVec (Pinv c.β γ c.κ c.σ c.li)
    (|Cu| + |c.σ| * (|c.istar| + |Cr|))
  have hwb : MBoundedV (shift2 S) (wM c.β γ c.κ c.σ c.li u rn c.istar) := by
    refine ⟨max Kw 0, fun s => ?_⟩
    filter_upwards [hCu (s + 2), hCr (s + 2)] with ω eu er k
    rcases k with j | j
    · refine (hKw _ (fun l => ?_) j).trans (le_max_left _ _)
      have h1 : |u (s + 2) ω| ≤ |Cu| := eu.trans (le_abs_self _)
      have h2 : |rn (s + 2) ω| ≤ |Cr| := er.trans (le_abs_self _)
      have h3 : |c.istar - rn (s + 2) ω| ≤ |c.istar| + |Cr| :=
        (abs_sub _ _).trans (add_le_add le_rfl h2)
      fin_cases l
      · simp only [Fvec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, abs_neg]
        nlinarith [abs_nonneg c.σ, abs_nonneg c.istar, abs_nonneg Cr]
      · simp only [Fvec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          abs_mul]
        nlinarith [abs_nonneg c.σ, abs_nonneg Cu, abs_nonneg (c.istar - rn (s + 2) ω)]
      · simp only [Fvec, Fin.reduceFinMk, Matrix.cons_val, abs_zero]
        nlinarith [abs_nonneg c.σ, abs_nonneg c.istar, abs_nonneg Cr, abs_nonneg Cu]
    · simp [wM, wPos]
  have hwa : MAdaptedV (shift2 S) (wM c.β γ c.κ c.σ c.li u rn c.istar) := by
    intro s k
    change StronglyMeasurable[S.𝓕 (s + 2)] _
    rcases k with j | j
    · have e : (fun ω => wM c.β γ c.κ c.σ c.li u rn c.istar s ω (Sum.inl j)) = fun ω =>
          Pinv c.β γ c.κ c.σ c.li j 0 * -u (s + 2) ω +
            Pinv c.β γ c.κ c.σ c.li j 1 * (c.σ * (c.istar - rn (s + 2) ω)) +
            Pinv c.β γ c.κ c.σ c.li j 2 * 0 := by
        funext ω
        simp [wM, wPos, Fvec, mulVec, dotProduct, Fin.sum_univ_three]
      rw [e]
      exact (((hua (s + 2)).neg.const_mul _).add (((stronglyMeasurable_const.sub
        (hra (s + 2))).const_mul _).const_mul _)).add stronglyMeasurable_const
    · simp only [wM, wPos, Sum.elim_inr]
      exact stronglyMeasurable_const
  have hx0k : MKnownV (shift2 S) 0 (x0M p1 i1 i0 c.istar) := by
    intro j
    change StronglyMeasurable[S.𝓕 (0 + 2)] _
    have m1 : S.𝓕 1 ≤ S.𝓕 (0 + 2) := S.𝓕.mono (by norm_num)
    have m0 : S.𝓕 0 ≤ S.𝓕 (0 + 2) := S.𝓕.mono (by norm_num)
    fin_cases j
    · exact hp1.mono m1
    · exact (hi1.mono m1).sub stronglyMeasurable_const
    · exact (hi0.mono m0).sub stronglyMeasurable_const
  have hx0b : MBoundedRV (shift2 S) (x0M p1 i1 i0 c.istar) := by
    refine ⟨K + |c.istar|, ?_⟩
    filter_upwards [hK] with ω e j
    obtain ⟨k1, -, k3, k4⟩ := e
    fin_cases j
    · simp only [x0M, x0vec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [abs_nonneg c.istar]
    · simp only [x0M, x0vec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [abs_sub (i1 ω) c.istar]
    · simp only [x0M, x0vec, Fin.reduceFinMk, Matrix.cons_val]
      linarith [abs_sub (i0 ω) c.istar]
  obtain ⟨Y, hY⟩ := m_bk_exists hnu hd (TidyR5aLambdaXZero.Pos.genericX c.β γ c.κ c.σ c.li h hli)
    hwb hwa hx0k hx0b
  obtain ⟨hAS, hIS, hEu⟩ := eqsM hβ hγ (x1 := x1) hY
  obtain ⟨-, ha, -, -, ⟨M, hM⟩⟩ := hY
  set B := max (max M K) 0 with hB
  have hB1 : M ≤ B := (le_max_left M K).trans (le_max_left _ _)
  have hB2 : K ≤ B := (le_max_right M K).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  refine ⟨πM p1 Y, xM x1 Y, iM c.istar i1 i0 Y, fun k => ?_, fun k => ?_, fun k => ?_,
    ⟨B, fun k => ?_⟩, ⟨B, fun k => ?_⟩, ⟨B + |c.istar|, fun k => ?_⟩,
    hAS, hIS, ?_, rfl, rfl, rfl, rfl⟩
  · rcases k with _ | _ | s
    · exact stronglyMeasurable_const
    · exact hp1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact stronglyMeasurable_const
    · exact hx1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact hi0
    · exact hi1
    · exact (ha s _).add stronglyMeasurable_const
  · rcases k with _ | _ | s
    · exact ae_of_all _ fun ω => by simpa [πM] using hB0
    · filter_upwards [hK] with ω e
      exact e.1.trans hB2
    · filter_upwards [hM s] with ω e
      exact (e _).trans hB1
  · rcases k with _ | _ | s
    · exact ae_of_all _ fun ω => by simpa [xM] using hB0
    · filter_upwards [hK] with ω e
      exact e.2.1.trans hB2
    · filter_upwards [hM s] with ω e
      exact (e _).trans hB1
  · rcases k with _ | _ | s
    · filter_upwards [hK] with ω e
      have := e.2.2.2.trans hB2
      change |i0 ω| ≤ _
      linarith [abs_nonneg c.istar]
    · filter_upwards [hK] with ω e
      have := e.2.2.1.trans hB2
      change |i1 ω| ≤ _
      linarith [abs_nonneg c.istar]
    · filter_upwards [hM s] with ω e
      change |Y s ω (Sum.inl 2) + c.istar| ≤ _
      have := (e (Sum.inl 2)).trans hB1
      linarith [abs_add_le (Y s ω (Sum.inl 2)) c.istar]
  · intro t
    rw [hlx]
    exact hEu t

end PosM

/-! ### Existence for `γ = 0` -/

namespace ZeroM

open TidyR5aLambdaXZero.Zero (Abk Pinv Pm A1 A2 MXZ MXX Fvec wZ x0vec A2c)
open TidyR5aLambdaXZero.Pos (c0)

variable {β κ σ li : ℝ}

/-- Woodford (2003), p. 593: inflation from a path at `γ = 0`. -/
def πM (p1 : Ω → ℝ) (Y : ℕ → Ω → Fin 2 ⊕ Fin 2 → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => p1
  | s + 2 => fun ω => Y s ω (Sum.inl 0)

/-- Woodford (2003), p. 593: the output gap from a path at `γ = 0`. -/
def xM (x1 : Ω → ℝ) (Y : ℕ → Ω → Fin 2 ⊕ Fin 2 → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | 1 => x1
  | s + 2 => fun ω => Y s ω (Sum.inl 1)

variable (β κ σ li) in
/-- Woodford (2003), (3.16) at `γ = 0`: the interest rate from a path,
`i_{s+2} = i* + (κσ/λᵢ)π_{s+2} + A₂ı_{s+1} − β⁻¹ı_s`. -/
noncomputable def iM (istar : ℝ) (i1 i0 : Ω → ℝ) (Y : ℕ → Ω → Fin 2 ⊕ Fin 2 → ℝ) :
    ℕ → Ω → ℝ
  | 0 => i0
  | 1 => i1
  | s + 2 => fun ω => c0 κ σ li * Y s ω (Sum.inl 0) + A2c β κ σ * Y s ω (Sum.inr 0) -
      β⁻¹ * Y s ω (Sum.inr 1) + istar

variable (β σ) in
/-- Woodford (2003), App. C.1 (tool): the forcing at `γ = 0`, random vector ordering. -/
noncomputable def wM (u rn : ℕ → Ω → ℝ) (istar : ℝ) : ℕ → Ω → Fin 2 ⊕ Fin 2 → ℝ :=
  fun s ω k => wZ β σ u rn istar s k ω

/-- Woodford (2003), p. 593: the initial predetermined state `(ı₁, ı₀)` at `γ = 0`, random
vector ordering. -/
def x0M (i1 i0 : Ω → ℝ) (istar : ℝ) : Ω → Fin 2 → ℝ :=
  fun ω j => x0vec i1 i0 istar j ω

/-- Woodford (2003), p. 593 (tool), at `γ = 0`, with conditional expectations: the
predetermined block is a.s. `(ı_{n−1}, ı_{n−2})`. -/
theorem lagsM {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ} {i1 i0 : Ω → ℝ}
    {Y : ℕ → Ω → Fin 2 ⊕ Fin 2 → ℝ}
    (hY : MEquil (shift2 S) (Abk β κ σ li) (wM β σ u rn istar) (x0M i1 i0 istar) Y) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, Y s ω (Sum.inr 0) = iM β κ σ li istar i1 i0 Y (s + 1) ω - istar ∧
      Y s ω (Sum.inr 1) = iM β κ σ li istar i1 i0 Y s ω - istar := by
  obtain ⟨hS, ha, hpk, h0, hb⟩ := hY
  have hi := integrable_of_adapted hb ha
  induction s with
  | zero =>
    filter_upwards [h0] with ω e
    refine ⟨?_, ?_⟩
    · rw [e 0]
      rfl
    · rw [e 1]
      rfl
  | succ s ih =>
    have key : ∀ᵐ ω ∂S.μ, ∀ j, Y (s + 1) ω (Sum.inr j) =
        (MXZ κ σ li *ᵥ fun i => Y s ω (Sum.inl i)) j +
          (MXX β κ σ *ᵥ fun i => Y s ω (Sum.inr i)) j := by
      filter_upwards [hS s] with ω e j
      have hk : (shift2 S).E s (fun ω' => Y (s + 1) ω' (Sum.inr j)) ω = Y (s + 1) ω (Sum.inr j) :=
        congrFun ((shift2 S).E_of_stronglyMeasurable (hpk s j) (hi (s + 1) (Sum.inr j))) ω
      have e2 := congrFun e (Sum.inr j)
      change (shift2 S).E s (fun ω' => Y (s + 1) ω' (Sum.inr j)) ω = _ at e2
      rw [hk] at e2
      rw [e2]
      have hv : Y s ω = Sum.elim (fun i => Y s ω (Sum.inl i)) (fun i => Y s ω (Sum.inr i)) := by
        funext k
        rcases k with i | i <;> rfl
      rw [hv, Abk, fromBlocks_mulVec]
      simp [wM, wZ]
    filter_upwards [key, ih] with ω e ih
    refine ⟨?_, ?_⟩
    · rw [e 0]
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_two, iM]
      ring
    · rw [e 1]
      simp [MXZ, MXX, mulVec, dotProduct, Fin.sum_univ_two, ih.1]

/-- Woodford (2003), (2.6), (3.1) at `γ = 0`, date `n = s + 2`, a.s., from an equilibrium. -/
theorem rowsM (hβ : β ≠ 0) {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ}
    {x0 : Ω → Fin 2 → ℝ} {Y : ℕ → Ω → Fin 2 ⊕ Fin 2 → ℝ}
    (hY : MEquil (shift2 S) (Abk β κ σ li) (wM β σ u rn istar) x0 Y) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, Pm β σ *ᵥ (fun j => S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl j)) ω) =
      A1 κ σ li *ᵥ (fun j => Y s ω (Sum.inl j)) + A2 β κ σ *ᵥ (fun j => Y s ω (Sum.inr j)) +
        Fvec σ u rn istar s ω := by
  filter_upwards [hY.1 s] with ω e
  have hv : Y s ω = Sum.elim (fun i => Y s ω (Sum.inl i)) (fun i => Y s ω (Sum.inr i)) := by
    funext k
    rcases k with i | i <;> rfl
  have hE : (fun j => S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl j)) ω) = Pinv β σ *ᵥ
      (A1 κ σ li *ᵥ (fun j => Y s ω (Sum.inl j)) + A2 β κ σ *ᵥ (fun j => Y s ω (Sum.inr j)) +
        Fvec σ u rn istar s ω) := by
    funext j
    have := congrFun e (Sum.inl j)
    change S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl j)) ω = _ at this
    rw [this, hv, Abk, fromBlocks_mulVec]
    simp only [Pi.add_apply, Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr, wM, wZ,
      ← mulVec_mulVec, mulVec_add]
    rfl
  rw [hE, mulVec_mulVec, TidyR5aLambdaXZero.Zero.Pm_mul_Pinv β σ hβ, one_mulVec]

/-- **Woodford (2003), (2.6), (3.1), (3.16) at `γ = 0`, `λₓ = 0`, with conditional expectations,
from an equilibrium** (dates from `n = 2`). -/
theorem eqsM (hβ : β ≠ 0) {S : MeasExpectationSystem Ω} {u rn : ℕ → Ω → ℝ} {istar : ℝ}
    {p1 x1 i1 i0 : Ω → ℝ} {Y : ℕ → Ω → Fin 2 ⊕ Fin 2 → ℝ}
    (hY : MEquil (shift2 S) (Abk β κ σ li) (wM β σ u rn istar) (x0M i1 i0 istar) Y) :
    (∀ k, 2 ≤ k → ASm S β 0 κ u (πM p1 Y) (xM x1 Y) k) ∧
      (∀ k, 2 ≤ k → ISm S σ rn (πM p1 Y) (xM x1 Y) (iM β κ σ li istar i1 i0 Y) k) ∧
      ∀ t, EulerM S β 0 κ σ (fun k ω => iM β κ σ li istar i1 i0 Y k ω - istar)
        (fbigM S β 0 κ σ 0 li (πM p1 Y) (xM x1 Y)) t := by
  have hl := lagsM hY
  have hr := rowsM hβ hY
  obtain ⟨-, ha, -, -, hb⟩ := hY
  have hi : ∀ s k, Integrable (fun ω => Y s ω k) S.μ := fun s k =>
    integrable_of_adapted (S := shift2 S) hb ha s k
  have hm : ∀ s k, StronglyMeasurable[S.𝓕 (s + 2)] (fun ω => Y s ω k) := fun s k => ha s k
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun t => ?_⟩
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    have e1 : (fun ω' => πM p1 Y (s + 2 + 1) ω' - 0 * πM p1 Y (s + 2) ω') =
        fun ω' => 1 * Y (s + 1) ω' (Sum.inl 0) + 0 * Y s ω' (Sum.inl 0) + 0 := by
      funext ω'
      simp only [πM]
      ring
    filter_upwards [hr s, E_lin_known S (s + 2) 1 0 0 (hi (s + 1) (Sum.inl 0))
      (hm s (Sum.inl 0)) (hi s (Sum.inl 0))] with ω r e
    have r0 : β * S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 0)) ω =
        Y s ω (Sum.inl 0) + -(κ * Y s ω (Sum.inl 1)) + -u (s + 2) ω := by
      have h := congrFun r 0
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_two] at h
      linear_combination h
    rw [e1, e]
    simp only [πM, xM]
    linear_combination -r0
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 2 := ⟨k - 2, by omega⟩
    filter_upwards [hr s] with ω r
    have r1 : σ * S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 0)) ω +
        S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 1)) ω =
        σ * c0 κ σ li * Y s ω (Sum.inl 0) + Y s ω (Sum.inl 1) +
          σ * A2c β κ σ * Y s ω (Sum.inr 0) + -(σ * β⁻¹) * Y s ω (Sum.inr 1) +
          σ * (istar - rn (s + 2) ω) := by
      have h := congrFun r 1
      simp [Pm, A1, A2, Fvec, mulVec, dotProduct, Fin.sum_univ_two] at h
      linear_combination h
    change Y s ω (Sum.inl 1) = S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 1)) ω -
      σ * ((c0 κ σ li * Y s ω (Sum.inl 0) + A2c β κ σ * Y s ω (Sum.inr 0) -
        β⁻¹ * Y s ω (Sum.inr 1) + istar) - S.E (s + 2) (fun ω' => Y (s + 1) ω' (Sum.inl 0)) ω -
        rn (s + 2) ω)
    linear_combination -r1
  · have hALi : ∀ᵐ ω ∂S.μ, ALi β 0 κ σ (fun k ω => iM β κ σ li istar i1 i0 Y k ω - istar) t ω =
        (-c0 κ σ li) * Y t ω (Sum.inl 0) + 0 * Y t ω (Sum.inl 0) + 0 := by
      filter_upwards [hl t] with ω l
      simp only [ALi]
      rw [← l.1, ← l.2]
      simp only [iM, A2c]
      ring
    filter_upwards [S.E_congr hALi (t + 2), E_lin_known S (t + 2) (-c0 κ σ li) 0 0
      (hi t (Sum.inl 0)) (hm t (Sum.inl 0)) (hi t (Sum.inl 0))] with ω eA e
    have hk : S.E (t + 2) (fun ω => Y t ω (Sum.inl 0)) = fun ω => Y t ω (Sum.inl 0) :=
      S.E_of_stronglyMeasurable (hm t _) (hi t _)
    rw [eA, e, hk]
    simp only [fbigM, qtil, zero_div, zero_mul, add_zero, mul_zero, sub_zero, πM, c0]
    ring

/-- **Woodford (2003), p. 593, on a filtered probability space: existence at `γ = 0`,
`λₓ = 0`** (the Blanchard–Kahn matrix `TidyR5aLambdaXZero.Zero.Abk`, `m_bk_exists`). -/
theorem existsM (c : IRuleBasic.Calib) (hlx : c.lx = 0) (hβ0 : 0 < c.β) (hβ1 : c.β < 1)
    (hσ : 0 < c.σ) (hκ : 0 < c.κ) (hli : 0 < c.li) (S : MeasExpectationSystem Ω)
    {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u) (hub : BndM S u) (hra : AdaptedM S rn)
    (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ} (hh : HistoryM S p1 x1 i1 i0) :
    ∃ π x i, RuleSolM S c 0 u rn p1 x1 i1 i0 π x i := by
  have hβ := hβ0.ne'
  obtain ⟨hnu, hcount⟩ := TidyR5aLambdaXZero.Zero.bk_roots c.β c.κ c.σ c.li hβ0 hβ1 hσ hκ hli
  have hd : Module.finrank ℝ (boundedOrbits (Abk c.β c.κ c.σ c.li)) = Fintype.card (Fin 2) := by
    rw [BKInvariantSplit.finrank_eq_stableCount hnu, hcount, Fintype.card_fin]
  obtain ⟨hp1, hx1, hi1, hi0, K, hK⟩ := hh
  obtain ⟨Cu, hCu⟩ := hub
  obtain ⟨Cr, hCr⟩ := hrb
  obtain ⟨Kw, hKw⟩ := GeneralFOC.exists_bound_mulVec (Pinv c.β c.σ)
    (|Cu| + |c.σ| * (|c.istar| + |Cr|))
  have hwb : MBoundedV (shift2 S) (wM c.β c.σ u rn c.istar) := by
    refine ⟨max Kw 0, fun s => ?_⟩
    filter_upwards [hCu (s + 2), hCr (s + 2)] with ω eu er k
    rcases k with j | j
    · refine (hKw _ (fun l => ?_) j).trans (le_max_left _ _)
      have h2 : |rn (s + 2) ω| ≤ |Cr| := er.trans (le_abs_self _)
      have h3 : |c.istar - rn (s + 2) ω| ≤ |c.istar| + |Cr| :=
        (abs_sub _ _).trans (add_le_add le_rfl h2)
      have h1 : |u (s + 2) ω| ≤ |Cu| := eu.trans (le_abs_self _)
      fin_cases l
      · simp only [Fvec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, abs_neg]
        nlinarith [abs_nonneg c.σ, abs_nonneg c.istar, abs_nonneg Cr]
      · simp only [Fvec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          abs_mul]
        nlinarith [abs_nonneg c.σ, abs_nonneg Cu, abs_nonneg (c.istar - rn (s + 2) ω)]
    · simp [wM, wZ]
  have hwa : MAdaptedV (shift2 S) (wM c.β c.σ u rn c.istar) := by
    intro s k
    change StronglyMeasurable[S.𝓕 (s + 2)] _
    rcases k with j | j
    · have e : (fun ω => wM c.β c.σ u rn c.istar s ω (Sum.inl j)) = fun ω =>
          Pinv c.β c.σ j 0 * -u (s + 2) ω +
            Pinv c.β c.σ j 1 * (c.σ * (c.istar - rn (s + 2) ω)) := by
        funext ω
        simp [wM, wZ, Fvec, mulVec, dotProduct, Fin.sum_univ_two]
      rw [e]
      exact ((hua (s + 2)).neg.const_mul _).add (((stronglyMeasurable_const.sub
        (hra (s + 2))).const_mul _).const_mul _)
    · simp only [wM, wZ, Sum.elim_inr]
      exact stronglyMeasurable_const
  have hx0k : MKnownV (shift2 S) 0 (x0M i1 i0 c.istar) := by
    intro j
    change StronglyMeasurable[S.𝓕 (0 + 2)] _
    have m1 : S.𝓕 1 ≤ S.𝓕 (0 + 2) := S.𝓕.mono (by norm_num)
    have m0 : S.𝓕 0 ≤ S.𝓕 (0 + 2) := S.𝓕.mono (by norm_num)
    fin_cases j
    · exact (hi1.mono m1).sub stronglyMeasurable_const
    · exact (hi0.mono m0).sub stronglyMeasurable_const
  have hx0b : MBoundedRV (shift2 S) (x0M i1 i0 c.istar) := by
    refine ⟨K + |c.istar|, ?_⟩
    filter_upwards [hK] with ω e j
    obtain ⟨-, -, k3, k4⟩ := e
    fin_cases j
    · simp only [x0M, x0vec, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      linarith [abs_sub (i1 ω) c.istar]
    · simp only [x0M, x0vec, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [abs_sub (i0 ω) c.istar]
  obtain ⟨Y, hY⟩ := m_bk_exists hnu hd
    (TidyR5aLambdaXZero.Zero.genericX c.β c.κ c.σ c.li hβ0 hβ1 hσ hκ hli) hwb hwa hx0k hx0b
  obtain ⟨hAS, hIS, hEu⟩ := eqsM hβ (p1 := p1) (x1 := x1) hY
  obtain ⟨-, ha, -, -, ⟨M, hM⟩⟩ := hY
  set B := max (max M K) 0 with hB
  have hB1 : M ≤ B := (le_max_left M K).trans (le_max_left _ _)
  have hB2 : K ≤ B := (le_max_right M K).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  obtain ⟨Kc, hKc⟩ := GeneralFOC.exists_bound_mulVec
    (!![c0 c.κ c.σ c.li, A2c c.β c.κ c.σ, -c.β⁻¹] : Matrix (Fin 1) (Fin 3) ℝ) B
  refine ⟨πM p1 Y, xM x1 Y, iM c.β c.κ c.σ c.li c.istar i1 i0 Y, fun k => ?_, fun k => ?_,
    fun k => ?_, ⟨B, fun k => ?_⟩, ⟨B, fun k => ?_⟩, ⟨max (B + |c.istar|) (Kc + |c.istar|),
      fun k => ?_⟩, hAS, hIS, ?_, rfl, rfl, rfl, rfl⟩
  · rcases k with _ | _ | s
    · exact stronglyMeasurable_const
    · exact hp1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact stronglyMeasurable_const
    · exact hx1
    · exact ha s _
  · rcases k with _ | _ | s
    · exact hi0
    · exact hi1
    · exact ((((ha s _).const_mul _).add ((ha s _).const_mul _)).sub
        ((ha s _).const_mul _)).add stronglyMeasurable_const
  · rcases k with _ | _ | s
    · exact ae_of_all _ fun ω => by simpa [πM] using hB0
    · filter_upwards [hK] with ω e
      exact e.1.trans hB2
    · filter_upwards [hM s] with ω e
      exact (e _).trans hB1
  · rcases k with _ | _ | s
    · exact ae_of_all _ fun ω => by simpa [xM] using hB0
    · filter_upwards [hK] with ω e
      exact e.2.1.trans hB2
    · filter_upwards [hM s] with ω e
      exact (e _).trans hB1
  · rcases k with _ | _ | s
    · filter_upwards [hK] with ω e
      have := e.2.2.2.trans hB2
      change |i0 ω| ≤ _
      refine le_trans ?_ (le_max_left _ _)
      linarith [abs_nonneg c.istar]
    · filter_upwards [hK] with ω e
      have := e.2.2.1.trans hB2
      change |i1 ω| ≤ _
      refine le_trans ?_ (le_max_left _ _)
      linarith [abs_nonneg c.istar]
    · filter_upwards [hM s] with ω e
      refine le_trans ?_ (le_max_right _ _)
      have hv := hKc ![Y s ω (Sum.inl 0), Y s ω (Sum.inr 0), Y s ω (Sum.inr 1)] (fun l => by
        fin_cases l
        · exact (e _).trans hB1
        · exact (e _).trans hB1
        · exact (e _).trans hB1) 0
      have hv' : |c0 c.κ c.σ c.li * Y s ω (Sum.inl 0) + A2c c.β c.κ c.σ * Y s ω (Sum.inr 0) +
          -c.β⁻¹ * Y s ω (Sum.inr 1)| ≤ Kc := by
        have e3 : (!![c0 c.κ c.σ c.li, A2c c.β c.κ c.σ, -c.β⁻¹] *ᵥ
            ![Y s ω (Sum.inl 0), Y s ω (Sum.inr 0), Y s ω (Sum.inr 1)]) 0 =
            c0 c.κ c.σ c.li * Y s ω (Sum.inl 0) + A2c c.β c.κ c.σ * Y s ω (Sum.inr 0) +
              -c.β⁻¹ * Y s ω (Sum.inr 1) := by
          simp [mulVec, dotProduct, Fin.sum_univ_three]
        rw [← e3]
        exact hv
      change |c0 c.κ c.σ c.li * Y s ω (Sum.inl 0) + A2c c.β c.κ c.σ * Y s ω (Sum.inr 0) -
        c.β⁻¹ * Y s ω (Sum.inr 1) + c.istar| ≤ _
      have e2 : c0 c.κ c.σ c.li * Y s ω (Sum.inl 0) + A2c c.β c.κ c.σ * Y s ω (Sum.inr 0) -
          c.β⁻¹ * Y s ω (Sum.inr 1) = c0 c.κ c.σ c.li * Y s ω (Sum.inl 0) +
            A2c c.β c.κ c.σ * Y s ω (Sum.inr 0) + -c.β⁻¹ * Y s ω (Sum.inr 1) := by ring
      rw [e2]
      linarith [abs_add_le (c0 c.κ c.σ c.li * Y s ω (Sum.inl 0) +
        A2c c.β c.κ c.σ * Y s ω (Sum.inr 0) + -c.β⁻¹ * Y s ω (Sum.inr 1)) c.istar]
  · intro t
    rw [hlx]
    exact hEu t

end ZeroM

/-! ### Every `0 ≤ γ ≤ 1` -/

/-- **Woodford (2003), p. 593, on every filtered probability space: the rule system (3.16) at
`λₓ = 0` is determinate for every `0 ≤ γ ≤ 1`.** For every essentially bounded adapted
disturbance and every essentially bounded history known at the right dates, (2.6), (3.1), (3.16)
with `λₓ = 0` has an essentially bounded adapted solution with that history (with Mathlib's
conditional expectation), and every such solution agrees with it a.s. at every date `≥ 1`. -/
theorem rule_system_existsUniqueM_lx0 (c : IRuleBasic.Calib) (hlx : c.lx = 0) (hβ0 : 0 < c.β)
    (hβ1 : c.β < 1) (hσ : 0 < c.σ) (hκ : 0 < c.κ) (hli : 0 < c.li) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (S : MeasExpectationSystem Ω) {u rn : ℕ → Ω → ℝ} (hua : AdaptedM S u)
    (hub : BndM S u) (hra : AdaptedM S rn) (hrb : BndM S rn) {p1 x1 i1 i0 : Ω → ℝ}
    (hh : HistoryM S p1 x1 i1 i0) :
    ∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i ∧
      ∀ π' x' i', RuleSolM S c γ u rn p1 x1 i1 i0 π' x' i' →
        ∀ k, 1 ≤ k → π' k =ᵐ[S.μ] π k ∧ x' k =ᵐ[S.μ] x k ∧ i' k =ᵐ[S.μ] i k := by
  obtain ⟨π, x, i, hsol⟩ : ∃ π x i, RuleSolM S c γ u rn p1 x1 i1 i0 π x i := by
    rcases hγ0.lt_or_eq with h | h
    · exact PosM.existsM c hlx ⟨hσ, hκ, hβ0, hβ1, h, hγ1⟩ hli S hua hub hra hrb hh
    · subst h
      exact ZeroM.existsM c hlx hβ0 hβ1 hσ hκ hli S hua hub hra hrb hh
  exact ⟨π, x, i, hsol, fun π' x' i' hsol' => rule_system_uniqueM S c hβ0 hβ1 hκ.ne' hσ.ne'
    hli (le_of_eq hlx.symm) hsol' hsol⟩

end Woodford.OptimalPolicyRules.TidyR5aLambdaXZeroMeasure
