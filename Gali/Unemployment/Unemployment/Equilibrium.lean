/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Unemployment.UnemploymentDef
import Unemployment.Determinacy4

/-!
# Equilibrium with unemployment

Galí (2015), Chapter 7, §7.2, pp. 207–208. The equilibrium conditions are the Chapter 6
gap-form equations — the DIS (12), the price NKPC (13), the wage-gap identity (15) — with the
wage Phillips curve written in the unemployment gap, (14) `π^w_t = β E_t π^w_{t+1} − λ_w φ û_t`,
plus the static equation (16) `φ û_t = μ̂^w_t = ω̃_t − (σ + φ/(1 − α)) ỹ_t`.

Footnote 8: given (16), (14) is exactly the Chapter 6 wage equation (20)
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`, `κ_w = λ_w (σ + φ/(1 − α))`. Hence the
Chapter 7 system is the Chapter 6 system plus the static equation (16), which determines the
new variable `û` (for `φ ≠ 0`); bounded solutions correspond one-to-one, and determinacy
transfers in both directions.

The gap-form equations are restated from the Chapter 6 project (`GapForm`, `System`). The
matrix system (24), its solution concept and the p. 174 determinacy theorem come from this
project's `Unemployment.Determinacy4` (the Chapter 6 module copied in): `Par`, `bookPar`,
`Dyn.IsSol`, `Dyn.Determinate`, `Dyn.eq24_iff`, `determinacy_iff`. The transfer lemma
`determinate_iff_ch6` shows that the Chapter 7 system under any rule (23) is determinate iff
the Chapter 6 system is; with `determinacy_iff` this gives the unconditional
`determinacy_ch7_iff` and the determinacy of the Taylor rule (17), `rule17_determinate`.

## Main results

* `eq16_levels`: (16) from the levels: (8), (10), the wage markup definition, labour demand
  (9) and the natural allocation.
* `eq14_iff_eq20` (fn. 8): given (16), (14) ⇔ Chapter 6's (20).
* `ch7_iff_ch6`: the Chapter 7 system (12)–(16) ⇔ the Chapter 6 system (22), (18), (20), (21)
  together with `û_t = φ⁻¹ (ω̃_t − (σ + φ/(1 − α)) ỹ_t)`.
* `isSol7_iff`: the same at the level of the matrix system with initial condition,
  adaptedness and predeterminedness.
* `determinate_iff_ch6`: determinacy of the Chapter 7 system ⇔ determinacy of (24).
* `determinacy_ch7_iff`, `determinacy_ch7_iff_phiY_zero`: the Chapter 7 equilibrium is
  determinate iff `φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1` (p. 174 condition).
* `rule17_determinate`: under (17) (`φ_π = 1.5`, `φ_y = 0.125`) the Chapter 7 equilibrium is
  determinate for all admissible parameters, in particular at the baseline calibration.
-/

namespace Gali.Unemployment.Equilibrium

/-! ### (16) from the levels -/

/-- Galí (2015), eq. (16), p. 208: with the average wage markup
`μ^w_t = ω_t − (σ c_t + φ n_t + ξ)`, `c = y`, (8) `μ^w_t = φ u_t`, (10) `uⁿ = μ^w/φ`,
labour demand (9) `(1 − α) n = y − a` (also at the natural allocation) and the natural real
wage `ωⁿ = σ yⁿ + φ nⁿ + ξ + μ^w` (flexible wages: markup at its desired level), the
unemployment gap satisfies `φ (u_t − uⁿ) = μ^w_t − μ^w = ω̃_t − (σ + φ/(1 − α)) ỹ_t`. -/
theorem eq16_levels {σ φ α ξ μw a y yn n nn w wn u : ℝ} (hα1 : α ≠ 1) (hφ : φ ≠ 0)
    (hn : (1 - α) * n = y - a) (hnn : (1 - α) * nn = yn - a)
    (hwn : wn = σ * yn + φ * nn + ξ + μw) (h8 : w - (σ * y + φ * n + ξ) = φ * u) :
    φ * (u - UnemploymentDef.natRate μw φ) = (w - (σ * y + φ * n + ξ)) - μw ∧
      (w - (σ * y + φ * n + ξ)) - μw = (w - wn) - (σ + φ / (1 - α)) * (y - yn) := by
  have h1 : 1 - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hα1)
  refine ⟨?_, ?_⟩
  · rw [h8, ← UnemploymentDef.markupGap_eq hφ]
  · have hy : y - yn = (1 - α) * (n - nn) := by linear_combination -hn + hnn
    have hq : φ / (1 - α) * (y - yn) = φ * (n - nn) := by
      rw [hy]
      field_simp
    rw [add_mul, hq, hwn]
    ring

/-! ### The gap-form equations (12)–(16) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (12), p. 207 (Chapter 6 eq. (22), restated): the DIS in gaps,
`ỹ_t = −σ⁻¹ (i_t − E_t π^p_{t+1} − rⁿ_t) + E_t ỹ_{t+1}`. -/
def DISGap (σ : ℝ) (ygap i pp rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (pp (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), eq. (13), p. 207 (Chapter 6 eq. (18), restated): the price NKPC in gaps,
`π^p_t = β E_t π^p_{t+1} + κ_p ỹ_t + λ_p ω̃_t`. -/
def PriceGapNKPC (β κp lamP : ℝ) (pp ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pp t = β • 𝔼.E t (pp (t + 1)) + κp • ygap t + lamP • wgap t

/-- Galí (2015), Chapter 6 eq. (20), p. 172 (restated; fn. 8 of Chapter 7):
`π^w_t = β E_t π^w_{t+1} + κ_w ỹ_t − λ_w ω̃_t`. -/
def WageGapNKPC (β κw lamW : ℝ) (pw ygap wgap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) + κw • ygap t - lamW • wgap t

/-- Galí (2015), eq. (14), p. 207: the wage Phillips curve in the unemployment gap,
`π^w_t = β E_t π^w_{t+1} − λ_w φ û_t`. -/
def WageUnempNKPC (β lamW φ : ℝ) (pw uhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, pw t = β • 𝔼.E t (pw (t + 1)) - (lamW * φ) • uhat t

/-- Galí (2015), eq. (15), p. 207, in the lagged convention `wl t = ω̃_{t−1}`:
`ω̃_t = ω̃_{t−1} + π^w_t − π^p_t − Δωⁿ_t`. -/
def WageGapLaw (wl pp pw dwn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, wl (t + 1) = wl t + pw t - pp t - dwn t

/-- Galí (2015), eq. (16), p. 208: `φ û_t = ω̃_t − (σ + φ/(1 − α)) ỹ_t`; the parameter `sw`
stands for `σ + φ/(1 − α)`. -/
def UnempGapEq (φ sw : ℝ) (ygap wgap uhat : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φ • uhat t = wgap t - sw • ygap t

/-- Galí (2015), fn. 8, p. 208 (**(14) + (16) ⇔ (20)**): given (16) at every date,
the unemployment-gap wage Phillips curve (14) is equivalent to the Chapter 6 wage equation (20)
with `κ_w = λ_w (σ + φ/(1 − α)) = λ_w sw`. -/
theorem eq14_iff_eq20 {β lamW φ sw : ℝ} {pw ygap wgap uhat : ℕ → Ω → ℝ}
    (h16 : UnempGapEq φ sw ygap wgap uhat) :
    WageUnempNKPC 𝔼 β lamW φ pw uhat ↔ WageGapNKPC 𝔼 β (lamW * sw) lamW pw ygap wgap := by
  have hk : ∀ t, (lamW * φ) • uhat t = lamW • wgap t - (lamW * sw) • ygap t := fun t => by
    rw [mul_smul, h16 t, smul_sub, mul_smul]
  unfold WageUnempNKPC WageGapNKPC
  refine forall_congr' fun t => ?_
  rw [hk t]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Galí (2015), §6.2 (Chapter 6, p. 173): the Chapter 6 non-policy block (22), (18), (20),
(21) with `ω̃_t = wl (t + 1)` (restated from the Chapter 6 project, `System.Equilibrium`). -/
def Ch6Equilibrium (σ β κp κw lamP lamW : ℝ) (ygap pp pw wl i rn dwn : ℕ → Ω → ℝ) : Prop :=
  DISGap 𝔼 σ ygap i pp rn ∧ PriceGapNKPC 𝔼 β κp lamP pp ygap (fun t => wl (t + 1)) ∧
    WageGapNKPC 𝔼 β κw lamW pw ygap (fun t => wl (t + 1)) ∧ WageGapLaw wl pp pw dwn

/-- Galí (2015), §7.2, pp. 207–208: the Chapter 7 non-policy block (12)–(16) with
`ω̃_t = wl (t + 1)` and the unemployment gap `û`. -/
def Ch7Equilibrium (σ β κp lamP lamW φ sw : ℝ) (ygap pp pw wl uhat i rn dwn : ℕ → Ω → ℝ) :
    Prop :=
  DISGap 𝔼 σ ygap i pp rn ∧ PriceGapNKPC 𝔼 β κp lamP pp ygap (fun t => wl (t + 1)) ∧
    WageUnempNKPC 𝔼 β lamW φ pw uhat ∧ WageGapLaw wl pp pw dwn ∧
    UnempGapEq φ sw ygap (fun t => wl (t + 1)) uhat

/-- Galí (2015), §7.2 and fn. 8, pp. 207–208 (**the Chapter 7 system is the Chapter 6 system
plus the static equation (16)**): for `φ ≠ 0`, `(ỹ, π^p, π^w, ω̃, û)` solves (12)–(16) iff
`(ỹ, π^p, π^w, ω̃)` solves the Chapter 6 system (22), (18), (20), (21) with
`κ_w = λ_w (σ + φ/(1 − α))` and `û_t = φ⁻¹ (ω̃_t − (σ + φ/(1 − α)) ỹ_t)`. -/
theorem ch7_iff_ch6 {σ β κp lamP lamW φ sw : ℝ} (hφ : φ ≠ 0)
    {ygap pp pw wl uhat i rn dwn : ℕ → Ω → ℝ} :
    Ch7Equilibrium 𝔼 σ β κp lamP lamW φ sw ygap pp pw wl uhat i rn dwn ↔
      Ch6Equilibrium 𝔼 σ β κp (lamW * sw) lamP lamW ygap pp pw wl i rn dwn ∧
        ∀ t, uhat t = φ⁻¹ • (wl (t + 1) - sw • ygap t) := by
  have h16iff : UnempGapEq φ sw ygap (fun t => wl (t + 1)) uhat ↔
      ∀ t, uhat t = φ⁻¹ • (wl (t + 1) - sw • ygap t) := by
    unfold UnempGapEq
    refine forall_congr' fun t => ?_
    constructor
    · intro h
      rw [← h, smul_smul, inv_mul_cancel₀ hφ, one_smul]
    · intro h
      rw [h, smul_smul, mul_inv_cancel₀ hφ, one_smul]
  constructor
  · rintro ⟨hd, h13, h14, h15, h16⟩
    exact ⟨⟨hd, h13, (eq14_iff_eq20 𝔼 h16).mp h14, h15⟩, h16iff.mp h16⟩
  · rintro ⟨⟨hd, h18, h20, h21⟩, hu⟩
    have h16 := h16iff.mpr hu
    exact ⟨hd, h18, (eq14_iff_eq20 𝔼 h16).mpr h20, h21, h16⟩

/-! ### The Chapter 7 system and the transfer of determinacy -/

/-- Galí (2015), §7.2, pp. 207–208: `(x, û)` with `x_t = (ỹ_t, π^p_t, π^w_t, ω̃_{t−1})` solves
the Chapter 7 system: (12) with the rule (23) substituted (row 1 of (24)), the price NKPC (13),
the wage Phillips curve in the unemployment gap (14), the wage-gap identity (15) and the static
equation (16) `φ û_t = ω̃_t − sw ỹ_t` (`sw = σ + φ/(1 − α)`), with initial gap `ω̃_{−1}`, all
variables adapted and `ω̃_t` known at `t`. -/
def IsSol7 (P : Determinacy4.Par) (φ sw : ℝ) (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ)
    (x : ℕ → Fin 4 → Ω → ℝ) (uhat : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, (P.σ + P.φy) * x t 0 ω + P.φp * x t 1 ω + P.φw * x t 2 ω =
      P.σ * 𝔼.E t (x (t + 1) 0) ω + 𝔼.E t (x (t + 1) 1) ω + u t 0 ω) ∧
    (∀ t ω, x t 1 ω = P.β * 𝔼.E t (x (t + 1) 1) ω + P.κp * x t 0 ω
      + P.lamP * 𝔼.E t (x (t + 1) 3) ω) ∧
    (∀ t ω, x t 2 ω = P.β * 𝔼.E t (x (t + 1) 2) ω - P.lamW * φ * uhat t ω) ∧
    (∀ t ω, 𝔼.E t (x (t + 1) 3) ω = x t 3 ω + x t 2 ω - x t 1 ω - u t 1 ω) ∧
    (∀ t ω, φ * uhat t ω = 𝔼.E t (x (t + 1) 3) ω - sw * x t 0 ω) ∧
    x 0 3 = ω0 ∧ Determinacy4.Fwd.VAdapted 𝔼 x ∧ (∀ t, 𝔼.E t (x (t + 1) 3) = x (t + 1) 3) ∧
    𝔼.Adapted uhat

/-- Galí (2015), p. 208: the unemployment gap implied by (16),
`û_t = φ⁻¹ (ω̃_t − sw ỹ_t)`. -/
noncomputable def uhatOf (φ sw : ℝ) (x : ℕ → Fin 4 → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => φ⁻¹ • (x (t + 1) 3 - sw • x t 0)

/-- Galí (2015), §7.2 and fn. 8, pp. 207–208 (**solutions correspond**): for `φ ≠ 0` and
`κ_w = λ_w sw`, `(x, û)` solves the Chapter 7 system iff `x` solves the Chapter 6 system (24)
(`Determinacy4.Dyn.IsSol`: same forcing, same initial condition) and `û = φ⁻¹ (ω̃ − sw ỹ)`. -/
theorem isSol7_iff {P : Determinacy4.Par} {φ sw : ℝ} (hφ : φ ≠ 0) (hκ : P.κw = P.lamW * sw)
    (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ) (x : ℕ → Fin 4 → Ω → ℝ) (uhat : ℕ → Ω → ℝ) :
    IsSol7 𝔼 P φ sw u ω0 x uhat ↔
      Determinacy4.Dyn.IsSol 𝔼 P u ω0 x ∧ uhat = uhatOf φ sw x := by
  constructor
  · rintro ⟨h0, h1, h14, h3, h16, hi, hax, hpre, -⟩
    have hu : uhat = uhatOf φ sw x := by
      funext t ω
      have e := h16 t ω
      rw [hpre t] at e
      simp only [uhatOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      linarith
    refine ⟨⟨fun t => (Determinacy4.Dyn.eq24_iff 𝔼 P x u t).mpr fun ω =>
      ⟨h0 t ω, h1 t ω, ?_, h3 t ω⟩, hi, hax, hpre⟩, hu⟩
    rw [h14 t ω, mul_assoc, h16 t ω, hκ]
    ring
  · rintro ⟨⟨heq, hi, hax, hpre⟩, rfl⟩
    have hr := fun t => (Determinacy4.Dyn.eq24_iff 𝔼 P x u t).mp (heq t)
    have h16 : ∀ t ω, φ * uhatOf φ sw x t ω = 𝔼.E t (x (t + 1) 3) ω - sw * x t 0 ω := by
      intro t ω
      rw [hpre t]
      simp only [uhatOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
    refine ⟨fun t ω => (hr t ω).1, fun t ω => (hr t ω).2.1, fun t ω => ?_,
      fun t ω => (hr t ω).2.2.2, h16, hi, hax, hpre, fun t => ?_⟩
    · rw [mul_assoc, h16 t ω, (hr t ω).2.2.1, hκ]
      ring
    · simp only [uhatOf, map_smul, map_sub, hpre t, hax t 0]

/-- Galí (2015), p. 208 (tool): the unemployment gap implied by (16) is bounded when `x` is. -/
theorem uhatOf_bounded {φ sw : ℝ} {x : ℕ → Fin 4 → Ω → ℝ} (hx : Determinacy4.Fwd.VBounded x) :
    BoundedProc (uhatOf φ sw x) := by
  obtain ⟨M, hM⟩ := hx
  refine ⟨|φ⁻¹| * (M + |sw| * M), fun t ω => ?_⟩
  simp only [uhatOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc |x (t + 1) 3 ω - sw * x t 0 ω| ≤ |x (t + 1) 3 ω| + |sw * x t 0 ω| := abs_sub _ _
    _ ≤ M + |sw| * M := by
      rw [abs_mul]
      exact add_le_add (hM _ _ _) (mul_le_mul_of_nonneg_left (hM _ _ _) (abs_nonneg _))

/-- Galí (2015), §7.2: determinacy of the Chapter 7 system — for every bounded adapted forcing
and bounded initial real wage gap known at `0`, exactly one bounded solution `(x, û)`. -/
def Determinate7 (P : Determinacy4.Par) (φ sw : ℝ) : Prop :=
  ∀ (u : ℕ → Fin 2 → Ω → ℝ) (ω0 : Ω → ℝ), Determinacy4.Fwd.VBounded u →
    Determinacy4.Fwd.VAdapted 𝔼 u → (∃ M, ∀ x, |ω0 x| ≤ M) → 𝔼.E 0 ω0 = ω0 →
      ∃! p : (ℕ → Fin 4 → Ω → ℝ) × (ℕ → Ω → ℝ),
        IsSol7 𝔼 P φ sw u ω0 p.1 p.2 ∧ Determinacy4.Fwd.VBounded p.1 ∧ BoundedProc p.2

/-- Galí (2015), §7.2, pp. 207–208 (**the transfer lemma**): for `φ ≠ 0` and
`κ_w = λ_w (σ + φ/(1 − α))`, the Chapter 7 system with unemployment is determinate iff the
Chapter 6 system (24) is (`Determinacy4.Dyn.Determinate`), for every rule (23). -/
theorem determinate_iff_ch6 {P : Determinacy4.Par} {φ sw : ℝ} (hφ : φ ≠ 0)
    (hκ : P.κw = P.lamW * sw) :
    Determinate7 𝔼 P φ sw ↔ Determinacy4.Dyn.Determinate 𝔼 P := by
  constructor
  · intro h7 u ω0 hub hua hω0 hω0a
    obtain ⟨⟨x, uh⟩, ⟨hs, hbx, -⟩, huniq⟩ := h7 u ω0 hub hua hω0 hω0a
    have hs6 := ((isSol7_iff 𝔼 hφ hκ u ω0 x uh).mp hs).1
    refine ⟨x, ⟨hs6, hbx⟩, ?_⟩
    rintro y ⟨hy, hby⟩
    have := huniq (y, uhatOf φ sw y)
      ⟨(isSol7_iff 𝔼 hφ hκ u ω0 y _).mpr ⟨hy, rfl⟩, hby, uhatOf_bounded hby⟩
    exact congrArg Prod.fst this
  · intro h6 u ω0 hub hua hω0 hω0a
    obtain ⟨x, ⟨hs, hbx⟩, huniq⟩ := h6 u ω0 hub hua hω0 hω0a
    refine ⟨(x, uhatOf φ sw x),
      ⟨(isSol7_iff 𝔼 hφ hκ u ω0 x _).mpr ⟨hs, rfl⟩, hbx, uhatOf_bounded hbx⟩, ?_⟩
    rintro ⟨y, uy⟩ ⟨hy, hby, -⟩
    obtain ⟨hy6, rfl⟩ := (isSol7_iff 𝔼 hφ hκ u ω0 y uy).mp hy
    rw [huniq y ⟨hy6, hby⟩]

/-! ### Determinacy of the equilibrium with unemployment (pp. 174, 208–210) -/

/-- **Galí (2015), §7.2 with the p. 174 theorem — determinacy with unemployment.** Let
`0 < β < 1`, `σ > 0`, `φ > 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0`, `φ_p, φ_w, φ_y ≥ 0` and
`κ_p = α λ_p/(1 − α)`, `κ_w = λ_w (σ + φ/(1 − α))` (`Determinacy4.bookPar`). The equilibrium of
the Chapter 7 system (12)–(16) under rule (23) is determinate (unique bounded `(x, û)` for every
bounded adapted forcing and bounded initial real wage gap) iff
`φ_p + φ_w + φ_y (1 − β)/Θ_y (1/λ_p + 1/λ_w) > 1`, `Θ_y = σ + (α + φ)/(1 − α)`. -/
theorem determinacy_ch7_iff [Nonempty Ω] {β σ φ α lamP lamW φp φw φy : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP)
    (hlw : 0 < lamW) (hfp : 0 ≤ φp) (hfw : 0 ≤ φw) (hfy : 0 ≤ φy) :
    Determinate7 𝔼 (Determinacy4.bookPar β σ φ α lamP lamW φp φw φy) φ (σ + φ / (1 - α)) ↔
      1 < φp + φw + φy * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
  rw [determinate_iff_ch6 𝔼 hφ.ne' rfl]
  exact Determinacy4.determinacy_iff 𝔼 hβ0 hβ1 hσ hφ.le hα0 hα1 hlp hlw hfp hfw hfy

/-- Galí (2015), p. 174 with `φ_y = 0`, §7.2: the Chapter 7 equilibrium under
`i_t = ρ + φ_p π^p_t + φ_w π^w_t + v_t` is determinate iff `φ_p + φ_w > 1`. -/
theorem determinacy_ch7_iff_phiY_zero [Nonempty Ω] {β σ φ α lamP lamW φp φw : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hlp : 0 < lamP) (hlw : 0 < lamW) (hfp : 0 ≤ φp) (hfw : 0 ≤ φw) :
    Determinate7 𝔼 (Determinacy4.bookPar β σ φ α lamP lamW φp φw 0) φ (σ + φ / (1 - α)) ↔
      1 < φp + φw := by
  rw [determinate_iff_ch6 𝔼 hφ.ne' rfl]
  exact Determinacy4.determinacy_iff_phiY_zero 𝔼 hβ0 hβ1 hσ hφ.le hα0 hα1 hlp hlw hfp hfw

/-- Galí (2015), eq. (17), p. 210: under the Taylor rule
`i_t = 0.01 + 1.5 π^p_t + 0.125 ŷ_t + v_t` (rule (23) with `φ_p = 1.5`, `φ_w = 0`,
`φ_y = 0.125`) the Chapter 7 equilibrium with unemployment is determinate for all
`0 < β < 1`, `σ > 0`, `φ > 0`, `0 ≤ α < 1`, `λ_p, λ_w > 0` — in particular at the book's
baseline calibration. -/
theorem rule17_determinate [Nonempty Ω] {β σ φ α lamP lamW : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 < φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hlp : 0 < lamP) (hlw : 0 < lamW) :
    Determinate7 𝔼 (Determinacy4.bookPar β σ φ α lamP lamW (3 / 2) 0 (1 / 8)) φ
      (σ + φ / (1 - α)) := by
  rw [determinacy_ch7_iff 𝔼 hβ0 hβ1 hσ hφ hα0 hα1 hlp hlw (by norm_num) le_rfl (by norm_num)]
  have h1α : 0 < 1 - α := by linarith
  have hΘ : 0 < σ + (α + φ) / (1 - α) := by positivity
  have : 0 ≤ 1 / 8 * (1 - β) / (σ + (α + φ) / (1 - α)) * (1 / lamP + 1 / lamW) := by
    have : 0 < 1 - β := by linarith
    positivity
  linarith

end Gali.Unemployment.Equilibrium
