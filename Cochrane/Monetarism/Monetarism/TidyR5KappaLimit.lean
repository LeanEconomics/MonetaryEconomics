/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR5MoneyRule
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The flexible-price limit `κ → ∞` of Galí's sticky-price money-rule equilibria

Cochrane (2023), Ch. 19, §19.1, p. 435 (the New-Keynesian sticky-price alternative to the
monetarist models) and §19.2, pp. 436–438 (the flexible-price money-growth model). Galí's
(2015) money-rule system (34) (`LinksTidy.GaliMoneyRule.System34`) has a Phillips curve with
slope `κ`; `κ = ∞` is price flexibility. This module proves that, as `κ → ∞`, the unique bounded
equilibrium of (34) (`TidyR5MoneyRule.system34_existsUnique`) converges, uniformly over dates and
states, to the unique flexible-price equilibrium (`LinksTidy.GaliMoneyRule.flex_existsUnique`),
with an explicit `O(1/κ)` rate, for every `ExpectationSystem`.

## The estimate

Write `d_t = l̂^κ_{t−1} − l̂^f_{t−1}` (so `d_0 = 0`) and `g_t = π^f_t − βE_tπ^f_{t+1}` (the
residual of the flexible-price inflation path in the zero-gap Phillips curve). Subtracting the
two models gives, exactly (`gap_identity_dis`, `gap_identity_nkpc`),
`(1+ση)ỹ_t = σηE_tỹ_{t+1} + (1+η)d_{t+1} − ηE_td_{t+2}` and
`κỹ_t = d_t − (1+β)d_{t+1} + βE_td_{t+2} + g_t`. With `Y, D, G` the suprema of `|ỹ|, |d|, |g|`,
the first gives `D ≤ (1+2ση)Y` and the second `κY ≤ (2+2β)D + G`; hence for
`κ > c = (2+2β)(1+2ση)` (`gapConst`):
`|ỹ_t| ≤ G/(κ−c)`, `|l̂^κ − l̂^f| ≤ (1+2ση)G/(κ−c)`, `|π^κ − π^f| ≤ 2(1+2ση)G/(κ−c)`
(`sticky_flex_bound`). The bound applies to ANY bounded equilibrium of (34), so it needs no
determinacy; the determinacy theorems make the limit statement one about THE equilibria.

## Main results

* `sticky_flex_bound`: the explicit `O(1/κ)` bound.
* `tendstoUniformly_of_family`, `kappa_limit`: uniform convergence of the gap to `0` and of
  inflation and real balances to their flexible-price values as `κ → ∞`.
* Link with the zero-gap results of `LinksTidy`: `sticky_eq_flex_iff` — the sticky-price
  equilibrium coincides with the flexible-price one at some (equivalently every) `κ > 0` iff
  `g ≡ 0` (`LinksTidy.GaliMoneyRule.equil34_zero_gap_iff`); `gap_never_zero` — in the example of
  `LinksTidy.GaliMoneyRule.flex_not_zero_gap_eq34` (`β ≠ 1`) the output gap is not identically
  zero at ANY finite `κ`, so the limit is genuinely a limit.
-/

namespace Cochrane.Monetarism.TidyR5KappaLimit

open Filter Topology LinksTidy.GaliMoneyRule

variable {Ω : Type*}

/-! ### Sup norms -/

/-- Cochrane (2023), §19.2, p. 436 (tool): the sup norm `sup_{t,ω} |x_t(ω)|` of a process (zero
for an unbounded process; used only for bounded ones). -/
noncomputable def supAbs (x : ℕ → Ω → ℝ) : ℝ := ⨆ p : ℕ × Ω, |x p.1 p.2|

/-- Cochrane (2023), §19.2, p. 436 (tool): a bounded process is bounded by its sup norm. -/
theorem le_supAbs {x : ℕ → Ω → ℝ} (hx : BoundedProc x) (t : ℕ) (ω : Ω) :
    |x t ω| ≤ supAbs x := by
  obtain ⟨M, hM⟩ := hx
  refine le_ciSup (f := fun p : ℕ × Ω => |x p.1 p.2|) ⟨M, ?_⟩ (t, ω)
  rintro _ ⟨p, rfl⟩
  exact hM p.1 p.2

/-- Cochrane (2023), §19.2, p. 436 (tool): the sup norm is below every nonnegative bound. -/
theorem supAbs_le {x : ℕ → Ω → ℝ} {a : ℝ} (h : ∀ t ω, |x t ω| ≤ a) (ha : 0 ≤ a) :
    supAbs x ≤ a :=
  Real.iSup_le (fun p => h p.1 p.2) ha

/-- Cochrane (2023), §19.2, p. 436 (tool): the sup norm is nonnegative. -/
theorem supAbs_nonneg (x : ℕ → Ω → ℝ) : 0 ≤ supAbs x :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

/-- Cochrane (2023), §19.2, p. 436 (tool): `|kx| ≤ kB` for `k ≥ 0` and `|x| ≤ B`. -/
theorem abs_mul_le_of {k x B : ℝ} (hk : 0 ≤ k) (hx : |x| ≤ B) : |k * x| ≤ k * B := by
  rw [abs_mul, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left hx hk

variable (𝔼 : ExpectationSystem Ω)

/-! ### The two models subtracted -/

/-- Cochrane (2023), §19.1, p. 435, with Galí (2015), (22), p. 63: the residual
`g_t = π_t − βE_tπ_{t+1}` of an inflation path in the zero-gap Phillips curve. -/
noncomputable def nkpcResid (β : ℝ) (infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => infl t - β • 𝔼.E t (infl (t + 1))

/-- Cochrane (2023), §19.1, p. 435: the threshold `c = (2+2β)(1+2ση)` above which the explicit
`O(1/κ)` bound of `sticky_flex_bound` applies. -/
def gapConst (σ η β : ℝ) : ℝ := (2 + 2 * β) * (1 + 2 * (σ * η))

omit 𝔼 in
/-- Cochrane (2023), (19.4)–(19.5), p. 436 (Galí (2015), (33), p. 74): from the money-growth
identity, `π_t = l̂_{t−1} − l̂_t + Δm_t`; hence two paths with the same money growth have
`π_t − π'_t = d_t − d_{t+1}` with `d = l̂_{·−1} − l̂'_{·−1}`. -/
theorem infl_diff {infl L infl' L' dm : ℕ → Ω → ℝ} (h : RealBalanceId infl L dm)
    (h' : RealBalanceId infl' L' dm) (t : ℕ) (ω : Ω) :
    infl t ω - infl' t ω = (L t ω - L' t ω) - (L (t + 1) ω - L' (t + 1) ω) := by
  have a := congrFun (h t) ω
  have b := congrFun (h' t) ω
  simp only [Pi.add_apply, Pi.sub_apply] at a b
  linarith

/-- Cochrane (2023), (19.4)–(19.5), p. 436: with predetermined real balances,
`E_tπ_{t+1} = l̂_t − E_tl̂_{t+1} + E_tΔm_{t+1}`. -/
theorem E_infl {infl L dm : ℕ → Ω → ℝ} (h : RealBalanceId infl L dm) (hL : Predetermined 𝔼 L)
    (t : ℕ) : 𝔼.E t (infl (t + 1)) = L (t + 1) - 𝔼.E t (L (t + 2)) + 𝔼.E t (dm (t + 1)) := by
  have hi : infl (t + 1) = L (t + 1) - L (t + 2) + dm (t + 1) := by
    funext ω
    have := congrFun (h (t + 1)) ω
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    linarith
  rw [hi, map_add, map_sub, hL t]

/-- Cochrane (2023), §19.1–§19.2, pp. 435–436 (Galí (2015), (32), p. 74): subtracting the
flexible-price money block from Galí's (32), the output gap of a sticky-price path and the
real-balance gap `d = l̂ − l̂^f` satisfy
`(1+ση)ỹ_t = σηE_tỹ_{t+1} + (1+η)d_{t+1} − ηE_td_{t+2}`. -/
theorem gap_identity_dis {σ η : ℝ} {ygap infl L inflf Lf rn yn dm : ℕ → Ω → ℝ}
    (h32 : Eq32 𝔼 σ η ygap infl L rn yn) (hr : RealBalanceId infl L dm)
    (hL : Predetermined 𝔼 L) (hfb : FlexBlock 𝔼 η inflf Lf rn yn)
    (hfr : RealBalanceId inflf Lf dm) (hLf : Predetermined 𝔼 Lf) (t : ℕ) (ω : Ω) :
    (1 + σ * η) * ygap t ω = σ * η * 𝔼.E t (ygap (t + 1)) ω +
      (1 + η) * (L (t + 1) ω - Lf (t + 1) ω) - η * 𝔼.E t (L (t + 2) - Lf (t + 2)) ω := by
  have a := congrFun (h32 t) ω
  have b := congrFun (hfb t) ω
  have e1 := congrFun (E_infl 𝔼 hr hL t) ω
  have e2 := congrFun (E_infl 𝔼 hfr hLf t) ω
  have e3 := congrFun (map_sub (𝔼.E t) (L (t + 2)) (Lf (t + 2))) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a b e1 e2 e3
  rw [e3]
  linear_combination a + b + η * e1 - η * e2

/-- Cochrane (2023), §19.1, p. 435 (Galí (2015), (22), p. 63): subtracting the flexible-price
inflation path from the sticky-price Phillips curve,
`κỹ_t = d_t − (1+β)d_{t+1} + βE_td_{t+2} + g_t` with `g = nkpcResid` of the flexible path. -/
theorem gap_identity_nkpc {β κ : ℝ} {ygap infl L inflf Lf dm : ℕ → Ω → ℝ}
    (hpc : NKPC 𝔼 β κ infl ygap) (hr : RealBalanceId infl L dm) (hL : Predetermined 𝔼 L)
    (hfr : RealBalanceId inflf Lf dm) (hLf : Predetermined 𝔼 Lf) (t : ℕ) (ω : Ω) :
    κ * ygap t ω = (L t ω - Lf t ω) - (1 + β) * (L (t + 1) ω - Lf (t + 1) ω) +
      β * 𝔼.E t (L (t + 2) - Lf (t + 2)) ω + nkpcResid 𝔼 β inflf t ω := by
  have a := congrFun (hpc t) ω
  have d := infl_diff hr hfr t ω
  have e1 := congrFun (E_infl 𝔼 hr hL t) ω
  have e2 := congrFun (E_infl 𝔼 hfr hLf t) ω
  have e3 := congrFun (map_sub (𝔼.E t) (L (t + 2)) (Lf (t + 2))) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a e1 e2 e3
  simp only [nkpcResid, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [e3]
  linear_combination -a + d - β * e1 + β * e2

/-! ### The explicit bound -/

/-- **Cochrane (2023), §19.1, p. 435, and §19.2, p. 436: the `O(1/κ)` bound.** Let
`σ, η, β ≥ 0` and `κ > c = (2+2β)(1+2ση)`. If `(ỹ, π, l̂)` is ANY bounded equilibrium of Galí's
(2015) sticky-price money-rule system (34) (`LinksTidy.GaliMoneyRule.Equil34`) and `(π^f, l̂^f)`
the flexible-price equilibrium (`LinksTidy.GaliMoneyRule.FlexEquil`) with the same shocks and
`l̂_{−1}`, then at every date and state, with `G = sup|π^f_t − βE_tπ^f_{t+1}|`:
`|ỹ_t| ≤ G/(κ−c)`, `|l̂_{t−1} − l̂^f_{t−1}| ≤ (1+2ση)G/(κ−c)` and
`|π_t − π^f_t| ≤ 2(1+2ση)G/(κ−c)`. -/
theorem sticky_flex_bound {σ η β κ L0 : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hβ : 0 ≤ β)
    (hκ : gapConst σ η β < κ) {rn yn dm ygap infl L inflf Lf : ℕ → Ω → ℝ}
    (hS : Equil34 𝔼 σ η β κ L0 rn yn dm ygap infl L)
    (hF : FlexEquil 𝔼 η L0 rn yn dm inflf Lf) (t : ℕ) (ω : Ω) :
    |ygap t ω| ≤ supAbs (nkpcResid 𝔼 β inflf) / (κ - gapConst σ η β) ∧
      |L t ω - Lf t ω| ≤
        (1 + 2 * (σ * η)) * supAbs (nkpcResid 𝔼 β inflf) / (κ - gapConst σ η β) ∧
      |infl t ω - inflf t ω| ≤
        2 * (1 + 2 * (σ * η)) * supAbs (nkpcResid 𝔼 β inflf) / (κ - gapConst σ η β) := by
  obtain ⟨hsys, hp, h0, -, -, -, hby, -, hbL⟩ := hS
  obtain ⟨⟨hfb, hfr⟩, hpf, hf0, -, -, hbif, hbLf⟩ := hF
  obtain ⟨h32, hpc, hr⟩ := (system34_iff 𝔼 hp).mp hsys
  have hsη : 0 ≤ σ * η := mul_nonneg hσ hη
  have hc : 0 < gapConst σ η β := by unfold gapConst; positivity
  have hκc : 0 < κ - gapConst σ η β := by linarith
  have hκ0 : 0 < κ := by linarith
  -- boundedness of the residual and of the real-balance gap
  have hbG : BoundedProc (nkpcResid 𝔼 β inflf) := by
    obtain ⟨M, hM⟩ := hbif
    refine ⟨M + β * M, fun s ν => ?_⟩
    have e := abs_mul_le_of hβ (𝔼.abs_E_le (fun ν => hM (s + 1) ν) s ν)
    simp only [nkpcResid, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨a1, a2⟩ := abs_le.mp (hM s ν)
    obtain ⟨b1, b2⟩ := abs_le.mp e
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hbd : BoundedProc (fun s => L s - Lf s) := by
    obtain ⟨M1, h1⟩ := hbL
    obtain ⟨M2, h2⟩ := hbLf
    refine ⟨M1 + M2, fun s ν => ?_⟩
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (h1 s ν) (h2 s ν))
  set G := supAbs (nkpcResid 𝔼 β inflf) with hGdef
  set Y := supAbs ygap with hYdef
  set D := supAbs (fun s => L s - Lf s) with hDdef
  have hG0 : 0 ≤ G := supAbs_nonneg _
  have hY0 : 0 ≤ Y := supAbs_nonneg _
  have hD0 : 0 ≤ D := supAbs_nonneg _
  have hyb : ∀ s ν, |ygap s ν| ≤ Y := le_supAbs hby
  have hdb : ∀ s ν, |L s ν - Lf s ν| ≤ D := fun s ν => by
    have := le_supAbs hbd s ν
    simpa only [Pi.sub_apply] using this
  have hgb : ∀ s ν, |nkpcResid 𝔼 β inflf s ν| ≤ G := le_supAbs hbG
  have hEy : ∀ s ν, |𝔼.E s (ygap (s + 1)) ν| ≤ Y := fun s ν =>
    𝔼.abs_E_le (fun ν => hyb (s + 1) ν) s ν
  have hEd : ∀ s ν, |𝔼.E s (L (s + 2) - Lf (s + 2)) ν| ≤ D := fun s ν =>
    𝔼.abs_E_le (fun ν => by simpa only [Pi.sub_apply] using hdb (s + 2) ν) s ν
  -- step 1: D ≤ (1+2ση)Y
  have step1 : D ≤ (1 + 2 * (σ * η)) * Y := by
    have hb : ∀ s ν, |L s ν - Lf s ν| ≤ ((1 + 2 * (σ * η)) * Y + η * D) / (1 + η) := by
      intro s ν
      rw [le_div_iff₀ (by linarith)]
      cases s with
      | zero =>
        rw [h0, hf0, sub_self, abs_zero, zero_mul]
        positivity
      | succ k =>
        have a := gap_identity_dis 𝔼 h32 hr hp hfb hfr hpf k ν
        have t1 := abs_mul_le_of (by linarith : (0 : ℝ) ≤ 1 + σ * η) (hyb k ν)
        have t2 := abs_mul_le_of hsη (hEy k ν)
        have t3 := abs_mul_le_of hη (hEd k ν)
        have hm : |L (k + 1) ν - Lf (k + 1) ν| * (1 + η) =
            |(1 + η) * (L (k + 1) ν - Lf (k + 1) ν)| := by
          rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + η), mul_comm]
        rw [hm]
        obtain ⟨a1, a2⟩ := abs_le.mp t1
        obtain ⟨b1, b2⟩ := abs_le.mp t2
        obtain ⟨c1, c2⟩ := abs_le.mp t3
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 : D ≤ ((1 + 2 * (σ * η)) * Y + η * D) / (1 + η) := supAbs_le hb (by positivity)
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  -- step 2: κY ≤ (2+2β)D + G
  have step2 : κ * Y ≤ (2 + 2 * β) * D + G := by
    have hb : ∀ s ν, |ygap s ν| ≤ ((2 + 2 * β) * D + G) / κ := by
      intro s ν
      rw [le_div_iff₀ hκ0]
      have a := gap_identity_nkpc 𝔼 hpc hr hp hfr hpf s ν
      have t1 := abs_mul_le_of (by linarith : (0 : ℝ) ≤ 1 + β) (hdb (s + 1) ν)
      have t2 := abs_mul_le_of hβ (hEd s ν)
      have hm : |ygap s ν| * κ = |κ * ygap s ν| := by
        rw [abs_mul, abs_of_pos hκ0, mul_comm]
      rw [hm]
      obtain ⟨a1, a2⟩ := abs_le.mp t1
      obtain ⟨b1, b2⟩ := abs_le.mp t2
      obtain ⟨c1, c2⟩ := abs_le.mp (hdb s ν)
      obtain ⟨d1, d2⟩ := abs_le.mp (hgb s ν)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h1 : Y ≤ ((2 + 2 * β) * D + G) / κ := supAbs_le hb (by positivity)
    rw [le_div_iff₀ hκ0] at h1
    linarith
  -- combine
  have hYb : Y ≤ G / (κ - gapConst σ η β) := by
    rw [le_div_iff₀ hκc]
    have : (2 + 2 * β) * D ≤ (2 + 2 * β) * ((1 + 2 * (σ * η)) * Y) :=
      mul_le_mul_of_nonneg_left step1 (by linarith)
    unfold gapConst
    nlinarith
  have hq : 0 ≤ 1 + 2 * (σ * η) := by linarith
  have hDb : D ≤ (1 + 2 * (σ * η)) * G / (κ - gapConst σ η β) := by
    rw [mul_div_assoc]
    exact step1.trans (mul_le_mul_of_nonneg_left hYb hq)
  refine ⟨(hyb t ω).trans hYb, (hdb t ω).trans hDb, ?_⟩
  rw [infl_diff hr hfr t ω]
  have e1 := hdb t ω
  have e2 := hdb (t + 1) ω
  have e3 : 2 * (1 + 2 * (σ * η)) * G / (κ - gapConst σ η β) =
      2 * ((1 + 2 * (σ * η)) * G / (κ - gapConst σ η β)) := by ring
  rw [e3]
  exact (abs_sub _ _).trans (by linarith)

/-! ### The limit -/

/-- **Cochrane (2023), §19.1, p. 435, and §19.2, pp. 436–437: the `κ → ∞` limit.** Let
`σ, η, β ≥ 0` and let `v κ = (ỹ^κ, π^κ, l̂^κ)` be bounded equilibria of Galí's (2015)
sticky-price money-rule system (34) for all large `κ`, and `(π^f, l̂^f)` the flexible-price
equilibrium with the same shocks and `l̂_{−1}`. Then, uniformly over dates and states, as
`κ → ∞`: `ỹ^κ → 0`, `π^κ → π^f` and `l̂^κ → l̂^f`. -/
theorem tendstoUniformly_of_family {σ η β L0 : ℝ} (hσ : 0 ≤ σ) (hη : 0 ≤ η) (hβ : 0 ≤ β)
    {rn yn dm inflf Lf : ℕ → Ω → ℝ}
    (v : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ))
    (hv : ∀ᶠ κ in atTop, Equil34 𝔼 σ η β κ L0 rn yn dm (v κ).1 (v κ).2.1 (v κ).2.2)
    (hF : FlexEquil 𝔼 η L0 rn yn dm inflf Lf) :
    TendstoUniformly (fun κ (p : ℕ × Ω) => (v κ).1 p.1 p.2) (fun _ => 0) atTop ∧
      TendstoUniformly (fun κ (p : ℕ × Ω) => (v κ).2.1 p.1 p.2) (fun p => inflf p.1 p.2)
        atTop ∧
      TendstoUniformly (fun κ (p : ℕ × Ω) => (v κ).2.2 p.1 p.2) (fun p => Lf p.1 p.2) atTop := by
  set G := supAbs (nkpcResid 𝔼 β inflf)
  set c := gapConst σ η β
  set q := 1 + 2 * (σ * η)
  have hq : 1 ≤ q := by have := mul_nonneg hσ hη; simp only [q]; linarith
  have hG0 : 0 ≤ G := supAbs_nonneg _
  -- the common bound `2qG/(κ−c)` is eventually below any `ε`
  have key : ∀ ε > 0, ∀ᶠ κ in atTop, gapConst σ η β < κ ∧
      Equil34 𝔼 σ η β κ L0 rn yn dm (v κ).1 (v κ).2.1 (v κ).2.2 ∧
      2 * q * G / (κ - c) < ε := by
    intro ε hε
    filter_upwards [hv, eventually_gt_atTop (c + (2 * q * G + 1) / ε)] with κ hκv hκ
    have hpos : 0 < (2 * q * G + 1) / ε := by positivity
    have hκc : 0 < κ - c := by linarith
    refine ⟨by linarith, hκv, ?_⟩
    rw [div_lt_iff₀ hκc]
    have h1 : (2 * q * G + 1) / ε * ε = 2 * q * G + 1 := div_mul_cancel₀ _ hε.ne'
    have h2 : (2 * q * G + 1) / ε * ε < (κ - c) * ε :=
      mul_lt_mul_of_pos_right (by linarith) hε
    linarith
  refine ⟨?_, ?_, ?_⟩ <;> rw [Metric.tendstoUniformly_iff] <;> intro ε hε <;>
    filter_upwards [key ε hε] with κ ⟨hκ, hκv, hlt⟩ <;> rintro ⟨t, ω⟩ <;>
    obtain ⟨b1, b2, b3⟩ := sticky_flex_bound 𝔼 hσ hη hβ hκ hκv hF t ω <;>
    rw [Real.dist_eq]
  · have hle : G / (κ - c) ≤ 2 * q * G / (κ - c) := by
      have hκc : 0 < κ - c := by linarith
      refine (div_le_div_iff_of_pos_right hκc).mpr ?_
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * q by linarith) hG0
      linarith
    rw [zero_sub, abs_neg]
    exact lt_of_le_of_lt (b1.trans hle) hlt
  · rw [abs_sub_comm]
    exact lt_of_le_of_lt b3 hlt
  · have hle : q * G / (κ - c) ≤ 2 * q * G / (κ - c) := by
      have hκc : 0 < κ - c := by linarith
      refine (div_le_div_iff_of_pos_right hκc).mpr ?_
      have := mul_nonneg (show (0 : ℝ) ≤ q by linarith) hG0
      linarith
    rw [abs_sub_comm]
    exact lt_of_le_of_lt (b2.trans hle) hlt

/-- **Cochrane (2023), §19.1, p. 435, and §19.2, pp. 436–437, under Galí's (2015) equilibrium
notion, p. 75: the flexible-price limit of the sticky-price money-rule equilibria.** For
`σ > 0`, `η ≥ 0`, `0 < β ≤ 1`, bounded adapted shocks and any `l̂_{−1}`: there is exactly one
bounded flexible-price equilibrium `(π^f, l̂^f)`; for every `κ > 0` exactly one bounded
equilibrium `v κ` of (34), and the family `κ ↦ v κ` is unique on `κ > 0`; and as `κ → ∞`,
`v κ → (0, π^f, l̂^f)` uniformly over dates and states. -/
theorem kappa_limit {σ η β : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {rn yn dm : ℕ → Ω → ℝ} (hrnb : BoundedProc rn) (hynb : BoundedProc yn)
    (hdmb : BoundedProc dm) (hrna : 𝔼.Adapted rn) (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm)
    (L0 : ℝ) :
    ∃ f : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), FlexEquil 𝔼 η L0 rn yn dm f.1 f.2 ∧
      (∀ f' : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), FlexEquil 𝔼 η L0 rn yn dm f'.1 f'.2 → f' = f) ∧
      ∃ v : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
        (∀ κ, 0 < κ → Equil34 𝔼 σ η β κ L0 rn yn dm (v κ).1 (v κ).2.1 (v κ).2.2) ∧
        (∀ w : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
          (∀ κ, 0 < κ → Equil34 𝔼 σ η β κ L0 rn yn dm (w κ).1 (w κ).2.1 (w κ).2.2) →
            ∀ κ, 0 < κ → w κ = v κ) ∧
        TendstoUniformly (fun κ (p : ℕ × Ω) => (v κ).1 p.1 p.2) (fun _ => 0) atTop ∧
        TendstoUniformly (fun κ (p : ℕ × Ω) => (v κ).2.1 p.1 p.2) (fun p => f.1 p.1 p.2)
          atTop ∧
        TendstoUniformly (fun κ (p : ℕ × Ω) => (v κ).2.2 p.1 p.2) (fun p => f.2 p.1 p.2)
          atTop := by
  obtain ⟨f, hf, hfu⟩ := flex_existsUnique 𝔼 hη hrnb hynb hdmb hrna hyna hdma L0
  have hex : ∀ κ, 0 < κ → ∃! v : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      Equil34 𝔼 σ η β κ L0 rn yn dm v.1 v.2.1 v.2.2 := fun κ hκ =>
    TidyR5MoneyRule.system34_existsUnique 𝔼 hσ hη hκ hβ0 hβ1 hrnb hynb hdmb hrna hyna hdma L0
  classical
  let v : ℝ → (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) := fun κ =>
    if h : 0 < κ then (hex κ h).exists.choose else (0, 0, 0)
  have hvE : ∀ κ, 0 < κ → Equil34 𝔼 σ η β κ L0 rn yn dm (v κ).1 (v κ).2.1 (v κ).2.2 := by
    intro κ hκ
    simp only [v, hκ, ↓reduceDIte]
    exact (hex κ hκ).exists.choose_spec
  have hev : ∀ᶠ κ in atTop, Equil34 𝔼 σ η β κ L0 rn yn dm (v κ).1 (v κ).2.1 (v κ).2.2 := by
    filter_upwards [eventually_gt_atTop 0] with κ hκ
    exact hvE κ hκ
  obtain ⟨u1, u2, u3⟩ := tendstoUniformly_of_family 𝔼 hσ.le hη hβ0.le v hev hf
  refine ⟨f, hf, hfu, v, hvE, fun w hw κ hκ => (hex κ hκ).unique (hw κ hκ) (hvE κ hκ), u1, u2,
    u3⟩

/-! ### Link with the zero-gap results -/

/-- Cochrane (2023), §19.1–§19.2, pp. 435–436, linking `LinksTidy.GaliMoneyRule`'s zero-gap
results: for any `κ` and any expectation system, the flexible-price equilibrium with a zero gap,
`(0, π^f, l̂^f)`, is an equilibrium of Galí's sticky-price system (34) iff the flexible-price
inflation path satisfies the zero-gap Phillips curve `π^f_t = βE_tπ^f_{t+1}` (`g ≡ 0`). Under
determinacy (`TidyR5MoneyRule.system34_existsUnique`) it is then THE equilibrium, so in that
case the `κ → ∞` limit is attained at every `κ > 0`, and only then. -/
theorem sticky_eq_flex_iff {σ η β κ L0 : ℝ} {rn yn dm inflf Lf : ℕ → Ω → ℝ}
    (hF : FlexEquil 𝔼 η L0 rn yn dm inflf Lf) :
    Equil34 𝔼 σ η β κ L0 rn yn dm (fun _ _ => 0) inflf Lf ↔ nkpcResid 𝔼 β inflf = 0 := by
  rw [equil34_zero_gap_iff]
  constructor
  · rintro ⟨-, h⟩
    funext t
    simp only [nkpcResid, Pi.zero_apply]
    rw [← h t, sub_self]
  · intro h
    refine ⟨hF, fun t => ?_⟩
    have := congrFun h t
    simp only [nkpcResid, Pi.zero_apply] at this
    exact sub_eq_zero.mp this

/-- Cochrane (2023), §19.1–§19.2, pp. 435–436: under determinacy, the unique sticky-price
equilibrium at a given `κ > 0` equals the zero-gap flexible-price equilibrium iff `g ≡ 0`
(`sticky_eq_flex_iff`), whatever `κ`. -/
theorem unique_sticky_eq_flex_iff {σ η β κ L0 : ℝ} (hσ : 0 < σ) (hη : 0 ≤ η) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) {rn yn dm inflf Lf ygap infl L : ℕ → Ω → ℝ}
    (hrnb : BoundedProc rn) (hynb : BoundedProc yn) (hdmb : BoundedProc dm)
    (hrna : 𝔼.Adapted rn) (hyna : 𝔼.Adapted yn) (hdma : 𝔼.Adapted dm)
    (hF : FlexEquil 𝔼 η L0 rn yn dm inflf Lf)
    (hS : Equil34 𝔼 σ η β κ L0 rn yn dm ygap infl L) :
    (ygap = (fun _ _ => 0) ∧ infl = inflf ∧ L = Lf) ↔ nkpcResid 𝔼 β inflf = 0 := by
  rw [← sticky_eq_flex_iff 𝔼 hF]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    exact hS
  · intro h
    obtain ⟨_, -, hu⟩ :=
      TidyR5MoneyRule.system34_existsUnique 𝔼 hσ hη hκ hβ0 hβ1 hrnb hynb hdmb hrna hyna hdma L0
    have e := (hu (ygap, infl, L) hS).trans (hu ((fun _ _ => 0), inflf, Lf) h).symm
    simp only [Prod.mk.injEq] at e
    exact e

/-- Cochrane (2023), §19.1–§19.2, pp. 435–436, in the example of
`LinksTidy.GaliMoneyRule.flex_not_zero_gap_eq34` (perfect foresight, `Δm ≡ 1`, `r̂ⁿ = ŷⁿ = 0`,
`l̂_{−1} = −η`, `η ≥ 0`, `β ≠ 1`): at EVERY `κ`, no bounded equilibrium of Galí's (34) has an
identically zero output gap. So the convergence of `kappa_limit` is not attained at any finite
`κ`; the flexible-price equilibrium is only the limit. -/
theorem gap_never_zero {σ η β κ : ℝ} (hη : 0 ≤ η) (hβ : β ≠ 1) {infl L : ℕ → Unit → ℝ}
    (hS : Equil34 perfectForesight σ η β κ (-η) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1)
      (fun _ _ => 0) infl L) : False := by
  obtain ⟨hflex, hnk⟩ := (equil34_zero_gap_iff perfectForesight).mp hS
  have hex := (flex_not_zero_gap_eq34 (σ := σ) (η := η) (κ := κ) hβ).1
  have hb0 : BoundedProc (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) := ⟨0, fun _ _ => by simp⟩
  have hb1 : BoundedProc (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) := ⟨1, fun _ _ => by simp⟩
  have ha : ∀ c : ℝ, perfectForesight.Adapted (fun (_ : ℕ) (_ : Unit) => c) := fun _ _ => rfl
  obtain ⟨_, -, hu⟩ := flex_existsUnique perfectForesight hη hb0 hb0 hb1 (ha 0) (ha 0) (ha 1)
    (-η)
  have e := (hu (infl, L) hflex).trans (hu ((fun _ _ => 1), (fun _ _ => -η)) hex).symm
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, -⟩ := e
  have := congrFun (hnk 0) ()
  change (1 : ℝ) = β * 1 at this
  exact hβ (by linarith)

end Cochrane.Monetarism.TidyR5KappaLimit
