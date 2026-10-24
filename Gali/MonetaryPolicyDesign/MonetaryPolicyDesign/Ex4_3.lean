/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Ex4_2

/-!
# Exercise 4.3: monetary policy and the effects of technology shocks

Galí (2015), Chapter 4, Exercise 4.3, pp. 121–122. The economy is
`y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ)`, `π_t = β E_t π_{t+1} + κ (y_t − y^n_t)`,
with the rule `i_t = ρ + φ_π π_t` (`φ_π > 1`), labour productivity `y_t − n_t = a_t`, technology
an AR(1) with persistence `ρ_a ∈ [0, 1)`, and natural output `y^n_t = ψ_y a_t` with `ψ_y > 1`.

Write `c = (1 − βρ_a) σ (1 − ρ_a) > 0` and `D = c + κ (φ_π − ρ_a)`.

## Main results

* **(a)** `ex4_3a_equilibrium_iff`: the unique equilibrium with bounded adapted output,
  inflation and employment is `y_t = γ_y a_t`, `π_t = γ_π a_t`, `n_t = γ_n a_t` with
  `γ_y = ψ_y κ (φ_π − ρ_a)/D`, `γ_π = −σ ψ_y (1 − ρ_a) κ/D`, `γ_n = γ_y − 1`
  (`gammaN_eq`: `γ_n = ((ψ_y − 1) κ (φ_π − ρ_a) − c)/D`).
* **(b)** `gammaY_mem`, `gammaPi_neg`: `0 < γ_y < ψ_y`, `γ_π < 0`. `ex4_3b_mono_phi`,
  `ex4_3b_mono_kappa`: `γ_y`, `γ_n` increase and `γ_π` rises towards `0` as `φ_π` increases;
  `γ_y`, `γ_n` increase and `γ_π` falls as `κ` increases (less price rigidity).
  `ex4_3b_phi_infty`: as `φ_π → ∞`, `γ_y → ψ_y`, `γ_π → 0`, `γ_n → ψ_y − 1` (the natural
  allocation). `ex4_3b_kappa_infty`: as `κ → ∞` (flexible prices), `γ_y → ψ_y`,
  `γ_n → ψ_y − 1`, `γ_π → −σ ψ_y (1 − ρ_a)/(φ_π − ρ_a)`. `ex4_3b_kappa_zero`: as `κ → 0`
  (fully rigid prices), `γ_y → 0`, `γ_π → 0`, `γ_n → −1`.
* **(c)** `ex4_3c_sign`: employment rises after a positive technology shock iff
  `(ψ_y − 1) κ (φ_π − ρ_a) > c`, and falls iff `<`. `ex4_3c_both_signs`: both occur
  (small `κ` gives a fall, large `φ_π` a rise). `ex4_3c_covariance`: the conditional
  covariance of output and employment is `γ_y γ_n var a`, so it has the sign of `γ_n`.
-/

namespace Gali.MonetaryPolicyDesign.Ex4_3

open Filter Topology Gali.MonetaryPolicyDesign.Ex4_1

/-! ### The MSV coefficients -/

/-- Galí (2015), Exercise 4.3(a): `c = (1 − βρ_a) σ (1 − ρ_a)`. -/
def cA (β σ ρa : ℝ) : ℝ := (1 - β * ρa) * σ * (1 - ρa)

/-- Galí (2015), Exercise 4.3(a): the denominator `D = (1 − βρ_a) σ (1 − ρ_a) + κ (φ_π − ρ_a)`. -/
def Da (β σ κ ρa φ : ℝ) : ℝ := cA β σ ρa + κ * (φ - ρa)

/-- Galí (2015), Exercise 4.3(a): the output response `γ_y = ψ_y κ (φ_π − ρ_a)/D`. -/
noncomputable def gammaY (β σ κ ρa ψy φ : ℝ) : ℝ := ψy * (κ * (φ - ρa)) / Da β σ κ ρa φ

/-- Galí (2015), Exercise 4.3(a): the inflation response `γ_π = −σ ψ_y (1 − ρ_a) κ/D`. -/
noncomputable def gammaPi (β σ κ ρa ψy φ : ℝ) : ℝ := -(σ * ψy * (1 - ρa)) * κ / Da β σ κ ρa φ

/-- Galí (2015), Exercise 4.3(a): the employment response `γ_n = γ_y − 1`. -/
noncomputable def gammaN (β σ κ ρa ψy φ : ℝ) : ℝ := gammaY β σ κ ρa ψy φ - 1

/-- Galí (2015), Exercise 4.3: `c > 0`. -/
theorem cA_pos {β σ ρa : ℝ} (hσ : 0 < σ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρa)
    (hρ1 : ρa < 1) : 0 < cA β σ ρa := by
  unfold cA
  have h1 : 0 < 1 - β * ρa := by nlinarith
  exact mul_pos (mul_pos h1 hσ) (by linarith)

/-- Galí (2015), Exercise 4.3: `D > 0` whenever `κ ≥ 0` and `φ_π ≥ ρ_a`. -/
theorem Da_pos {β σ κ ρa φ : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hφ : ρa ≤ φ) : 0 < Da β σ κ ρa φ := by
  unfold Da
  have := cA_pos hσ hβ1 hρ0 hρ1
  have : 0 ≤ κ * (φ - ρa) := mul_nonneg hκ (by linarith)
  linarith

/-- Galí (2015), Exercise 4.3(c): `γ_n = ((ψ_y − 1) κ (φ_π − ρ_a) − c)/D`. -/
theorem gammaN_eq {β σ κ ρa ψy φ : ℝ} (hD : Da β σ κ ρa φ ≠ 0) :
    gammaN β σ κ ρa ψy φ = ((ψy - 1) * (κ * (φ - ρa)) - cA β σ ρa) / Da β σ κ ρa φ := by
  unfold gammaN gammaY
  field_simp
  unfold Da
  ring

/-! ### The model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 4.3, pp. 121–122: an equilibrium: the DIS equation in output, the
NKPC with `y^n_t = ψ_y a_t`, the rule `i_t = ρ + φ_π π_t`, and `y_t − n_t = a_t`. -/
def Equilibrium (β σ κ ρ ψy φ : ℝ) (a y infl n i : ℕ → Ω → ℝ) : Prop :=
  (∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)) ∧
  (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • (y t - ψy • a t)) ∧
  (∀ t, i t = (fun _ => ρ) + φ • infl t) ∧
  (∀ t, y t - n t = a t)

/-- Galí (2015), Exercise 4.3: the equilibrium conditions are the structural system of the
output gap `ỹ = y − ψ_y a` (with `φ_y = 0` and forcing `u_t = −σ ψ_y (1 − ρ_a) a_t`), the
rule, and `n_t = y_t − a_t`. -/
theorem equilibrium_iff {β σ κ ρ ρa ψy φ : ℝ} (hσ : σ ≠ 0) {a y infl n i : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) :
    Equilibrium 𝔼 β σ κ ρ ψy φ a y infl n i ↔
      Structural 𝔼 β σ κ φ 0 (fun t => (-(σ * ψy * (1 - ρa))) • a t)
        (fun t => y t - ψy • a t) infl ∧
      (∀ t, i t = (fun _ => ρ) + φ • infl t) ∧ (∀ t, n t = y t - a t) := by
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  constructor
  · rintro ⟨hd, hp, hr, hn⟩
    refine ⟨fun t => ⟨?_, ?_⟩, hr, fun t => by rw [← hn t]; abel⟩
    · funext ω
      have e := congrFun (hd t) ω
      have r := congrFun (hr t) ω
      have ea := congrFun (ha.2 t) ω
      simp only [map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at e r ea ⊢
      rw [ea]
      linear_combination σ * e - (i t ω - 𝔼.E t (infl (t + 1)) ω - ρ) * hinv - r
    · rw [hp t]
  · rintro ⟨hs, hr, hn⟩
    refine ⟨fun t => ?_, fun t => (hs t).2, hr, fun t => by rw [hn t]; abel⟩
    funext ω
    have e := congrFun (hs t).1 ω
    have r := congrFun (hr t) ω
    have ea := congrFun (ha.2 t) ω
    simp only [map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e r ea ⊢
    rw [ea] at e
    linear_combination σ⁻¹ * e + σ⁻¹ * r - (y t ω - 𝔼.E t (y (t + 1)) ω) * hinv

/-- Galí (2015), Exercise 4.3(a): the MSV processes solve the structural system. -/
theorem msv_structural {β σ κ ρa ψy φ : ℝ} (hD : Da β σ κ ρa φ ≠ 0) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) :
    Structural 𝔼 β σ κ φ 0 (fun t => (-(σ * ψy * (1 - ρa))) • a t)
      (fun t => gammaY β σ κ ρa ψy φ • a t - ψy • a t)
      (fun t => gammaPi β σ κ ρa ψy φ • a t) := by
  have c1 : (σ + 0) * (gammaY β σ κ ρa ψy φ - ψy) + φ * gammaPi β σ κ ρa ψy φ
      = σ * ((gammaY β σ κ ρa ψy φ - ψy) * ρa) + gammaPi β σ κ ρa ψy φ * ρa
        - σ * ψy * (1 - ρa) := by
    unfold gammaY gammaPi
    field_simp
    unfold Da cA
    ring
  have c2 : gammaPi β σ κ ρa ψy φ
      = β * (gammaPi β σ κ ρa ψy φ * ρa) + κ * (gammaY β σ κ ρa ψy φ - ψy) := by
    unfold gammaY gammaPi
    field_simp
    unfold Da cA
    ring
  intro t
  simp only [map_sub, map_smul, ha.2 t, smul_smul]
  refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a t ω * c1
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a t ω * c2

/-- **Exercise 4.3(a)** (Galí 2015, p. 122): for `σ, κ > 0`, `0 < β < 1`, `0 ≤ ρ_a < 1` and
`φ_π > 1`, with bounded AR(1) technology, a tuple `(y, π, n, i)` with bounded adapted
`y, π, n` is an equilibrium iff `y_t = γ_y a_t`, `π_t = γ_π a_t`, `n_t = γ_n a_t` and
`i_t = ρ + φ_π π_t`. The MSV tuple is bounded and adapted, so it is the unique such
equilibrium (`ex4_3a_exists`). -/
theorem ex4_3a_equilibrium_iff {β σ κ ρ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hφ : 1 < φ) {a : ℕ → Ω → ℝ}
    (ha : 𝔼.IsAR1 ρa a) (hab : BoundedProc a) {y infl n i : ℕ → Ω → ℝ}
    (hay : 𝔼.Adapted y) (hai : 𝔼.Adapted infl) (hby : BoundedProc y)
    (hbi : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ ψy φ a y infl n i ↔
      y = (fun t => gammaY β σ κ ρa ψy φ • a t) ∧
      infl = (fun t => gammaPi β σ κ ρa ψy φ • a t) ∧
      n = (fun t => gammaN β σ κ ρa ψy φ • a t) ∧
      i = fun t => (fun _ => ρ) + φ • infl t := by
  have hD := (Da_pos hσ hκ.le hβ1 hρ0 hρ1 (by linarith) (φ := φ)).ne'
  rw [equilibrium_iff 𝔼 hσ.ne' ha]
  have hgapA : 𝔼.Adapted (fun t => y t - ψy • a t) :=
    fun t => by simp only [map_sub, map_smul, hay t, ha.1 t]
  have hgapB : BoundedProc (fun t => y t - ψy • a t) := by
    have := Ex4_2.bounded_comb hby hab 1 (-ψy)
    simpa [sub_eq_add_neg, neg_smul] using this
  have hmA : 𝔼.Adapted (fun t => gammaY β σ κ ρa ψy φ • a t - ψy • a t) :=
    fun t => by simp only [map_sub, map_smul, ha.1 t]
  have hmB : BoundedProc (fun t => gammaY β σ κ ρa ψy φ • a t - ψy • a t) := by
    have := Ex4_2.bounded_comb hab hab (gammaY β σ κ ρa ψy φ) (-ψy)
    simpa [sub_eq_add_neg, neg_smul] using this
  constructor
  · rintro ⟨hs, hr, hn⟩
    obtain ⟨h1, h2⟩ := structural_unique 𝔼 hσ hκ hβ0 hβ1 (by linarith) le_rfl
      (by nlinarith) hs (msv_structural 𝔼 hD ha) hgapA hai hmA (isAR1_smul 𝔼 ha _).1 hgapB
      hbi hmB (boundedProc_smul hab _)
    have hy : y = fun t => gammaY β σ κ ρa ψy φ • a t := by
      funext t
      have := congrFun h1 t
      simpa using this
    refine ⟨hy, h2, ?_, funext hr⟩
    funext t
    rw [hn t, hy]
    simp only [gammaN, sub_smul, one_smul]
  · rintro ⟨hy, hp, hn, hi⟩
    refine ⟨?_, fun t => by rw [hi], fun t => ?_⟩
    · rw [hy, hp]
      exact msv_structural 𝔼 hD ha
    · rw [hn, hy]
      simp only [gammaN, sub_smul, one_smul]

/-- **Exercise 4.3(a), existence** (Galí 2015, p. 122): whenever `D ≠ 0` the MSV tuple is an
equilibrium. -/
theorem ex4_3a_exists {β σ κ ρ ρa ψy φ : ℝ} (hσ : σ ≠ 0) (hD : Da β σ κ ρa φ ≠ 0)
    {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a) :
    Equilibrium 𝔼 β σ κ ρ ψy φ a (fun t => gammaY β σ κ ρa ψy φ • a t)
      (fun t => gammaPi β σ κ ρa ψy φ • a t) (fun t => gammaN β σ κ ρa ψy φ • a t)
      (fun t => (fun _ => ρ) + φ • (gammaPi β σ κ ρa ψy φ • a t)) := by
  rw [equilibrium_iff 𝔼 hσ ha]
  refine ⟨msv_structural 𝔼 hD ha, fun _ => rfl, fun t => ?_⟩
  simp only [gammaN, sub_smul, one_smul]

/-! ### Exercise 4.3(b): dependence on `φ_π` and `κ` -/

/-- Galí (2015), Exercise 4.3(b): `0 < γ_y < ψ_y` for `κ > 0`, `φ_π > ρ_a`. -/
theorem gammaY_mem {β σ κ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) (hφ : ρa < φ) :
    0 < gammaY β σ κ ρa ψy φ ∧ gammaY β σ κ ρa ψy φ < ψy := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hx : 0 < κ * (φ - ρa) := mul_pos hκ (by linarith)
  have hD : 0 < Da β σ κ ρa φ := by unfold Da; linarith
  unfold gammaY
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hD]
  unfold Da
  nlinarith

/-- Galí (2015), Exercise 4.3(b): `γ_π < 0`: a positive technology shock lowers inflation. -/
theorem gammaPi_neg {β σ κ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) (hφ : ρa ≤ φ) :
    gammaPi β σ κ ρa ψy φ < 0 := by
  have hD := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hφ
  unfold gammaPi
  apply div_neg_of_neg_of_pos _ hD
  have : 0 < σ * ψy * (1 - ρa) := mul_pos (mul_pos hσ hψ) (by linarith)
  nlinarith

/-- **Exercise 4.3(b), dependence on `φ_π`** (Galí 2015, p. 122): on `φ_π > ρ_a`, the output
and employment responses are strictly increasing in `φ_π` and the inflation response is
strictly increasing (towards zero). -/
theorem ex4_3b_mono_phi {β σ κ ρa ψy : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) :
    StrictMonoOn (gammaY β σ κ ρa ψy) (Set.Ioi ρa) ∧
      StrictMonoOn (gammaN β σ κ ρa ψy) (Set.Ioi ρa) ∧
      StrictMonoOn (gammaPi β σ κ ρa ψy) (Set.Ioi ρa) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hY : StrictMonoOn (gammaY β σ κ ρa ψy) (Set.Ioi ρa) := by
    intro x hx z hz hxz
    have hx' : ρa < x := hx
    have hz' : ρa < z := hz
    have hDx := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hx'.le (φ := x)
    have hDz := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hz'.le (φ := z)
    unfold gammaY
    rw [div_lt_div_iff₀ hDx hDz]
    unfold Da
    have : 0 < κ * (z - x) := mul_pos hκ (by linarith)
    have : 0 < ψy * cA β σ ρa * (κ * (z - x)) := by positivity
    nlinarith
  refine ⟨hY, fun x hx z hz hxz => ?_, fun x hx z hz hxz => ?_⟩
  · unfold gammaN
    linarith [hY hx hz hxz]
  · have hx' : ρa < x := hx
    have hz' : ρa < z := hz
    have hDx := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hx'.le (φ := x)
    have hDz := Da_pos hσ hκ.le hβ1 hρ0 hρ1 hz'.le (φ := z)
    unfold gammaPi
    rw [div_lt_div_iff₀ hDx hDz]
    unfold Da
    have : 0 < σ * ψy * (1 - ρa) * κ := mul_pos (mul_pos (mul_pos hσ hψ) (by linarith)) hκ
    have : 0 < σ * ψy * (1 - ρa) * κ * (κ * (z - x)) := mul_pos this (mul_pos hκ (by linarith))
    nlinarith

/-- **Exercise 4.3(b), dependence on `κ`** (Galí 2015, p. 122): for `φ_π > ρ_a`, on `κ > 0`
the output and employment responses are strictly increasing in `κ` (less rigid prices) and
the inflation response is strictly decreasing (more negative). -/
theorem ex4_3b_mono_kappa {β σ ρa ψy φ : ℝ} (hσ : 0 < σ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 0 < ψy) (hφ : ρa < φ) :
    StrictMonoOn (fun κ => gammaY β σ κ ρa ψy φ) (Set.Ioi 0) ∧
      StrictMonoOn (fun κ => gammaN β σ κ ρa ψy φ) (Set.Ioi 0) ∧
      StrictAntiOn (fun κ => gammaPi β σ κ ρa ψy φ) (Set.Ioi 0) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hm : 0 < φ - ρa := by linarith
  have hY : StrictMonoOn (fun κ => gammaY β σ κ ρa ψy φ) (Set.Ioi 0) := by
    intro x hx z hz hxz
    have hx' : (0 : ℝ) < x := hx
    have hz' : (0 : ℝ) < z := hz
    have hDx := Da_pos hσ hx'.le hβ1 hρ0 hρ1 hφ.le
    have hDz := Da_pos hσ hz'.le hβ1 hρ0 hρ1 hφ.le
    simp only [gammaY]
    rw [div_lt_div_iff₀ hDx hDz]
    unfold Da
    have : 0 < ψy * cA β σ ρa * ((z - x) * (φ - ρa)) := by
      have : 0 < (z - x) * (φ - ρa) := mul_pos (by linarith) hm
      positivity
    nlinarith
  refine ⟨hY, fun x hx z hz hxz => ?_, fun x hx z hz hxz => ?_⟩
  · simp only [gammaN]
    linarith [hY hx hz hxz]
  · have hx' : (0 : ℝ) < x := hx
    have hz' : (0 : ℝ) < z := hz
    have hDx := Da_pos hσ hx'.le hβ1 hρ0 hρ1 hφ.le
    have hDz := Da_pos hσ hz'.le hβ1 hρ0 hρ1 hφ.le
    simp only [gammaPi]
    rw [div_lt_div_iff₀ hDz hDx]
    unfold Da
    have : 0 < σ * ψy * (1 - ρa) * cA β σ ρa * (z - x) :=
      mul_pos (mul_pos (mul_pos (mul_pos hσ hψ) (by linarith)) hc) (by linarith)
    nlinarith

/-- **Exercise 4.3(b), strict inflation targeting** (Galí 2015, p. 122): as `φ_π → ∞`,
`γ_y → ψ_y`, `γ_π → 0` and `γ_n → ψ_y − 1`: the natural (flexible-price) allocation. -/
theorem ex4_3b_phi_infty (β σ ρa ψy : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (gammaY β σ κ ρa ψy) atTop (𝓝 ψy) ∧
      Tendsto (gammaPi β σ κ ρa ψy) atTop (𝓝 0) ∧
      Tendsto (gammaN β σ κ ρa ψy) atTop (𝓝 (ψy - 1)) := by
  set c := cA β σ ρa
  have hDa : ∀ φ, Da β σ κ ρa φ = (c - κ * ρa) + κ * φ := fun φ => by
    unfold Da
    ring
  have hev : ∀ᶠ φ in atTop, 0 < (c - κ * ρa) + κ * φ :=
    (tendsto_atTop_add_const_left _ (c - κ * ρa)
      (Tendsto.const_mul_atTop hκ tendsto_id)).eventually_gt_atTop 0
  have hY : Tendsto (gammaY β σ κ ρa ψy) atTop (𝓝 ψy) := by
    have := (Ex4_2.tendsto_div_affine (-(ψy * c)) (c - κ * ρa) hκ).const_add ψy
    rw [add_zero] at this
    refine this.congr' (hev.mono fun φ hφ => ?_)
    have hD := mul_inv_cancel₀ hφ.ne'
    simp only [gammaY, hDa]
    linear_combination -ψy * hD
  refine ⟨hY, ?_, ?_⟩
  · have := Ex4_2.tendsto_div_affine (-(σ * ψy * (1 - ρa)) * κ) (c - κ * ρa) hκ
    refine this.congr fun φ => ?_
    simp only [gammaPi, hDa]
  · exact hY.sub_const 1

/-- **Exercise 4.3(b), flexible prices** (Galí 2015, p. 122): for `φ_π > ρ_a`, as `κ → ∞`,
`γ_y → ψ_y`, `γ_n → ψ_y − 1` and `γ_π → −σ ψ_y (1 − ρ_a)/(φ_π − ρ_a)`. -/
theorem ex4_3b_kappa_infty (β σ ρa ψy : ℝ) {φ : ℝ} (hφ : ρa < φ) :
    Tendsto (fun κ => gammaY β σ κ ρa ψy φ) atTop (𝓝 ψy) ∧
      Tendsto (fun κ => gammaN β σ κ ρa ψy φ) atTop (𝓝 (ψy - 1)) ∧
      Tendsto (fun κ => gammaPi β σ κ ρa ψy φ) atTop
        (𝓝 (-(σ * ψy * (1 - ρa)) / (φ - ρa))) := by
  set c := cA β σ ρa
  have hm : 0 < φ - ρa := by linarith
  have hDa : ∀ κ, Da β σ κ ρa φ = c + (φ - ρa) * κ := fun κ => by
    unfold Da
    ring
  have hev : ∀ᶠ κ in atTop, 0 < c + (φ - ρa) * κ :=
    (tendsto_atTop_add_const_left _ c
      (Tendsto.const_mul_atTop hm tendsto_id)).eventually_gt_atTop 0
  have hY : Tendsto (fun κ => gammaY β σ κ ρa ψy φ) atTop (𝓝 ψy) := by
    have := (Ex4_2.tendsto_div_affine (-(ψy * c)) c hm).const_add ψy
    rw [add_zero] at this
    refine this.congr' (hev.mono fun κ hκ => ?_)
    have hD := mul_inv_cancel₀ hκ.ne'
    simp only [gammaY, hDa]
    linear_combination -ψy * hD
  refine ⟨hY, hY.sub_const 1, ?_⟩
  have := (Ex4_2.tendsto_div_affine (σ * ψy * (1 - ρa) * c / (φ - ρa)) c hm).const_add
    (-(σ * ψy * (1 - ρa)) / (φ - ρa))
  rw [add_zero] at this
  refine this.congr' (hev.mono fun κ hκ => ?_)
  have hD := mul_inv_cancel₀ hκ.ne'
  have hM := mul_inv_cancel₀ hm.ne'
  simp only [gammaPi, hDa]
  linear_combination σ * ψy * (1 - ρa) * (φ - ρa)⁻¹ * hD
    - σ * ψy * (1 - ρa) * κ * (c + (φ - ρa) * κ)⁻¹ * hM

/-- **Exercise 4.3(b), fully rigid prices** (Galí 2015, p. 122): as `κ → 0`, `γ_y → 0`,
`γ_π → 0` and `γ_n → −1`: output does not respond and employment falls one for one. -/
theorem ex4_3b_kappa_zero {β σ ρa ψy φ : ℝ} (hσ : 0 < σ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) :
    Tendsto (fun κ => gammaY β σ κ ρa ψy φ) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun κ => gammaPi β σ κ ρa ψy φ) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun κ => gammaN β σ κ ρa ψy φ) (𝓝 0) (𝓝 (-1)) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  have hden : Tendsto (fun κ : ℝ => Da β σ κ ρa φ) (𝓝 0) (𝓝 (cA β σ ρa)) := by
    have := (tendsto_const_nhds (x := cA β σ ρa)).add
      ((tendsto_id (x := (𝓝 (0 : ℝ)))).mul (tendsto_const_nhds (x := φ - ρa)))
    simp only [id, zero_mul, add_zero] at this
    exact this
  have hY : Tendsto (fun κ => gammaY β σ κ ρa ψy φ) (𝓝 0) (𝓝 0) := by
    have hnum : Tendsto (fun κ : ℝ => ψy * (κ * (φ - ρa))) (𝓝 0) (𝓝 0) := by
      have := (tendsto_const_nhds (x := ψy)).mul
        ((tendsto_id (x := (𝓝 (0 : ℝ)))).mul (tendsto_const_nhds (x := φ - ρa)))
      simpa using this
    have h := hnum.div hden hc.ne'
    rw [zero_div] at h
    exact h
  have hN := hY.sub_const 1
  rw [zero_sub] at hN
  refine ⟨hY, ?_, hN⟩
  have hnum : Tendsto (fun κ : ℝ => -(σ * ψy * (1 - ρa)) * κ) (𝓝 0) (𝓝 0) := by
    have := (tendsto_const_nhds (x := -(σ * ψy * (1 - ρa)))).mul
      (tendsto_id (x := (𝓝 (0 : ℝ))))
    simpa using this
  have h := hnum.div hden hc.ne'
  rw [zero_div] at h
  exact h

/-! ### Exercise 4.3(c): the employment response -/

/-- **Exercise 4.3(c)** (Galí 2015, p. 122): for `κ > 0` and `φ_π > ρ_a`, employment rises
after a positive technology shock iff `(ψ_y − 1) κ (φ_π − ρ_a) > (1 − βρ_a) σ (1 − ρ_a)`,
falls iff `<`, and is unchanged iff `=`. -/
theorem ex4_3c_sign {β σ κ ρa ψy φ : ℝ} (hσ : 0 < σ) (hκ : 0 ≤ κ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hφ : ρa ≤ φ) :
    (0 < gammaN β σ κ ρa ψy φ ↔ cA β σ ρa < (ψy - 1) * (κ * (φ - ρa))) ∧
      (gammaN β σ κ ρa ψy φ < 0 ↔ (ψy - 1) * (κ * (φ - ρa)) < cA β σ ρa) ∧
      (gammaN β σ κ ρa ψy φ = 0 ↔ (ψy - 1) * (κ * (φ - ρa)) = cA β σ ρa) := by
  have hD := Da_pos hσ hκ hβ1 hρ0 hρ1 hφ
  rw [gammaN_eq hD.ne']
  refine ⟨?_, ?_, ?_⟩
  · rw [div_pos_iff_of_pos_right hD, sub_pos]
  · rw [div_neg_iff, sub_neg]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · exact h
    · intro h
      exact Or.inr ⟨h, hD⟩
  · rw [div_eq_zero_iff, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · exact Or.inl

/-- **Exercise 4.3(c), both signs occur** (Galí 2015, p. 122): with `ψ_y > 1` and
`φ_π > ρ_a`, employment falls after a positive technology shock when prices are rigid
enough (small `κ > 0`) and rises when policy is aggressive enough (large `φ_π`). -/
theorem ex4_3c_both_signs {β σ ρa ψy : ℝ} (hσ : 0 < σ) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1) (hψ : 1 < ψy) :
    (∀ φ, ρa < φ → ∃ κ, 0 < κ ∧ gammaN β σ κ ρa ψy φ < 0) ∧
      (∀ κ, 0 < κ → ∃ φ, 1 < φ ∧ 0 < gammaN β σ κ ρa ψy φ) := by
  have hc := cA_pos hσ hβ1 hρ0 hρ1
  refine ⟨fun φ hφ => ?_, fun κ hκ => ?_⟩
  · have hm : 0 < (ψy - 1) * (φ - ρa) := mul_pos (by linarith) (by linarith)
    refine ⟨cA β σ ρa / ((ψy - 1) * (φ - ρa)) / 2, by positivity, ?_⟩
    refine ((ex4_3c_sign hσ (by positivity) hβ1 hρ0 hρ1 hφ.le).2.1).mpr ?_
    have : (ψy - 1) * (cA β σ ρa / ((ψy - 1) * (φ - ρa)) / 2 * (φ - ρa))
        = cA β σ ρa / 2 * (((ψy - 1) * (φ - ρa)) / ((ψy - 1) * (φ - ρa))) := by
      ring
    rw [this, div_self hm.ne', mul_one]
    linarith
  · have hk : 0 < (ψy - 1) * κ := mul_pos (by linarith) hκ
    set φ := ρa + 1 + cA β σ ρa / ((ψy - 1) * κ) with hφdef
    have hφ1 : 1 < φ := by
      have : 0 < cA β σ ρa / ((ψy - 1) * κ) := by positivity
      linarith
    refine ⟨φ, hφ1, ((ex4_3c_sign hσ hκ.le hβ1 hρ0 hρ1 (by linarith)).1).mpr ?_⟩
    have : (ψy - 1) * (κ * (φ - ρa))
        = (ψy - 1) * κ + cA β σ ρa * (((ψy - 1) * κ) / ((ψy - 1) * κ)) := by
      rw [hφdef]
      ring
    rw [this, div_self hk.ne', mul_one]
    linarith

/-- **Exercise 4.3(c), comovement** (Galí 2015, p. 122): for a covariance form `B`, in the
MSV equilibrium `cov(y_t, n_t) = γ_y γ_n var a_t`; with `0 < γ_y` (`gammaY_mem`) and
`var a_t > 0` its sign is the sign of `γ_n`, so output and employment move in opposite
directions conditional on technology exactly when `γ_n < 0`. -/
theorem ex4_3c_covariance (B : LinearMap.BilinForm ℝ (Ω → ℝ)) {β σ κ ρa ψy φ : ℝ}
    (hσ : 0 < σ) (hκ : 0 < κ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρa) (hρ1 : ρa < 1)
    (hψ : 0 < ψy) (hφ : ρa < φ) (x : Ω → ℝ) (hx : 0 < B x x) :
    B (gammaY β σ κ ρa ψy φ • x) (gammaN β σ κ ρa ψy φ • x)
        = gammaY β σ κ ρa ψy φ * gammaN β σ κ ρa ψy φ * B x x ∧
      (B (gammaY β σ κ ρa ψy φ • x) (gammaN β σ κ ρa ψy φ • x) < 0 ↔
        gammaN β σ κ ρa ψy φ < 0) := by
  have hcov : B (gammaY β σ κ ρa ψy φ • x) (gammaN β σ κ ρa ψy φ • x)
      = gammaY β σ κ ρa ψy φ * gammaN β σ κ ρa ψy φ * B x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hY := (gammaY_mem hσ hκ hβ1 hρ0 hρ1 hψ hφ).1
  refine ⟨hcov, ?_⟩
  rw [hcov, mul_comm (gammaY β σ κ ρa ψy φ), mul_assoc]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : 0 ≤ gammaN β σ κ ρa ψy φ * (gammaY β σ κ ρa ψy φ * B x x) :=
      mul_nonneg hn (mul_pos hY hx).le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos h (mul_pos hY hx)

end Gali.MonetaryPolicyDesign.Ex4_3
