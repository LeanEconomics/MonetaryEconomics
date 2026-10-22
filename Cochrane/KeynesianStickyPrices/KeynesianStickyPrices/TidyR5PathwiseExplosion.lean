/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5ExplosionsMeasure
import KeynesianStickyPrices.TidyR5ExpectationsMeasureIID

/-!
# Under genuine uncertainty the claim must be stated in expectation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5.2, p. 421: "real
explosions faster than the interest rate so `E_t βʲ x_{t+j} → ∞`", and the appeal to the real
transversality condition.

TidyR5ExplosionsMeasure characterises the book's claim in its expectational form. This module
shows that the expectational form is essential: read **pathwise** (realised discounted output
`βᵗ x̃_t(ω)`), the claim changes under genuine uncertainty. On the i.i.d. fair-coin probability
space (`TidyR5ExpectationsMeasureIID.iidSystem coin`), at `σ = 1`, `β = 1/2`, `κ = 1/4`,
`φ = 2 = 1/β`, `φ_x = 0`:

* every deviation satisfies the real transversality condition in expectation, at every date and
  almost every state (`all_expected_tvc`), because the perfect-foresight condition of
  `TidyR5RealExplosions.tvcX_fails_pf_iff` fails there;
* yet the deviation `xPath`, driven by inflation-neutral output innovations of growing scale
  `6^{t+1} ε_{t+1}`, solves the deviation system almost surely (`devM_path`) and its realised
  discounted output is **unbounded almost surely** (`realised_unbounded`), with
  `|βᵗ x̃_t| ≥ (5/8) 3ᵗ` for `t ≥ 1` on every path of `±1` shocks (`yPath_lower`).

`pathwise_explosion` collects the three statements. Pathwise real explosions are thus not
ruled out by the expected transversality condition: innovations, which the equilibrium
conditions leave free, can be arbitrarily large.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5PathwiseExplosion

open MeasureTheory Filter Topology TidyR5ExpectationsMeasure TidyR5ExpectationsMeasureIID
open TidyR5RealExplosions TidyR5ExplosionsMeasure

/-! ### The coin -/

/-- Cochrane (2023), Ch. 2, p. 29: the fair coin takes the values `±1` almost surely. -/
theorem coin_abs_one : ∀ᵐ x ∂(coin : Measure ℝ), |x| = 1 := by
  change ∀ᵐ x ∂coinMeasure, |x| = 1
  rw [ae_iff]
  have hs : MeasurableSet {x : ℝ | ¬ |x| = 1} :=
    (measurableSet_eq_fun continuous_abs.measurable measurable_const).compl
  simp only [coinMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hs,
    Set.indicator, Set.mem_ofPred_eq]
  norm_num

/-- Cochrane (2023), Ch. 2, p. 29: every coin shock is `±1` almost surely. -/
theorem shock_abs_one (t : ℕ) : ∀ᵐ ω ∂(iidSystem coin).μ, |shock t ω| = 1 :=
  (measurePreserving_eval_infinitePi (fun _ => (coin : Measure ℝ)) t).quasiMeasurePreserving.ae
    coin_abs_one

/-- Cochrane (2023), Ch. 2, p. 29: a coin shock is integrable. -/
theorem integrable_shock (t : ℕ) : Integrable (shock t) (iidSystem coin).μ :=
  MeasExpectationSystem.BddRV.integrable
    ⟨(measurable_pi_apply t).aestronglyMeasurable, 1, shock_ae_bdd coin coin_bdd t⟩

/-! ### The deviation -/

/-- Cochrane (2023), p. 421: discounted realised output `y_t = βᵗ x̃_t`, `y_0 = 0`,
`y_{t+1} = (3/4) y_t + 3^{t+1} ε_{t+1}`. -/
noncomputable def yPath : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => 3 / 4 * yPath t ω + 3 ^ (t + 1) * shock (t + 1) ω

/-- Cochrane (2023), p. 421: realised output `x̃_t = 2ᵗ y_t`, so
`x̃_{t+1} = (3/2) x̃_t + 6^{t+1} ε_{t+1}`. -/
noncomputable def xPath (t : ℕ) (ω : ℕ → ℝ) : ℝ := 2 ^ t * yPath t ω

/-- Cochrane (2023), p. 421: inflation `π̃_0 = 0`, `π̃_{t+1} = (π̃_t − κ x̃_t)/β` (known at `t`). -/
noncomputable def piPath : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => 2 * (piPath t ω - 1 / 4 * xPath t ω)

/-- The interest rate `ĩ_t = φ π̃_t = 2 π̃_t`. -/
noncomputable def iPath (t : ℕ) : (ℕ → ℝ) → ℝ := (2 : ℝ) • piPath t

/-- The real rate `r̃_t = ĩ_t − E_t π̃_{t+1}`. -/
noncomputable def rPath (t : ℕ) : (ℕ → ℝ) → ℝ :=
  iPath t - (iidSystem coin).E t (piPath (t + 1))

/-- `y_t` is known at `t`. -/
theorem measurable_yPath (t : ℕ) : Measurable[(iidSystem coin).𝓕 t] (yPath t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h1 : Measurable[(iidSystem coin).𝓕 (t + 1)] (yPath t) :=
      ih.mono ((iidSystem coin).𝓕.mono (Nat.le_succ t)) le_rfl
    have h2 := measurable_shock coin (le_refl (t + 1))
    exact (h1.const_mul _).add (h2.const_mul _)

/-- `x̃_t` is known at `t`. -/
theorem measurable_xPath (t : ℕ) : Measurable[(iidSystem coin).𝓕 t] (xPath t) :=
  (measurable_yPath t).const_mul _

/-- `π̃_{t+1}` is known at `t`. -/
theorem measurable_piPath (t : ℕ) : Measurable[(iidSystem coin).𝓕 t] (piPath (t + 1)) := by
  induction t with
  | zero =>
    exact (measurable_const.sub ((measurable_xPath 0).const_mul _)).const_mul _
  | succ t ih =>
    have h1 : Measurable[(iidSystem coin).𝓕 (t + 1)] (piPath (t + 1)) :=
      ih.mono ((iidSystem coin).𝓕.mono (Nat.le_succ t)) le_rfl
    exact (h1.sub ((measurable_xPath (t + 1)).const_mul _)).const_mul _

/-- `y_t` is integrable. -/
theorem integrable_yPath (t : ℕ) : Integrable (yPath t) (iidSystem coin).μ := by
  induction t with
  | zero => exact integrable_const _
  | succ t ih => exact (ih.const_mul _).add ((integrable_shock (t + 1)).const_mul _)

/-- `x̃_t` is integrable. -/
theorem integrable_xPath (t : ℕ) : Integrable (xPath t) (iidSystem coin).μ :=
  (integrable_yPath t).const_mul _

/-- `π̃_t` is integrable. -/
theorem integrable_piPath (t : ℕ) : Integrable (piPath t) (iidSystem coin).μ := by
  induction t with
  | zero => exact integrable_const _
  | succ t ih => exact (ih.sub ((integrable_xPath t).const_mul _)).const_mul _

/-- `E_t π̃_{t+1} = π̃_{t+1}` (inflation is predetermined one period ahead). -/
theorem E_piPath (t : ℕ) : (iidSystem coin).E t (piPath (t + 1)) = piPath (t + 1) :=
  (iidSystem coin).E_of_stronglyMeasurable (measurable_piPath t).stronglyMeasurable
    (integrable_piPath (t + 1))

/-- `E_t x̃_{t+1} = (3/2) x̃_t` almost surely (the output innovation has mean zero). -/
theorem E_xPath (t : ℕ) :
    (iidSystem coin).E t (xPath (t + 1)) =ᵐ[(iidSystem coin).μ] (3 / 2 : ℝ) • xPath t := by
  have hx : xPath (t + 1) = (3 / 2 : ℝ) • xPath t + (6 ^ (t + 1) : ℝ) • shock (t + 1) := by
    funext ω
    simp only [xPath, yPath, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (6 : ℝ) ^ (t + 1) = 2 ^ (t + 1) * 3 ^ (t + 1) by rw [← mul_pow]; norm_num, pow_succ]
    ring
  rw [hx]
  have hE := (iidSystem coin).E_of_stronglyMeasurable (measurable_xPath t).stronglyMeasurable
    (integrable_xPath t)
  filter_upwards [(iidSystem coin).E_add ((integrable_xPath t).smul (3 / 2 : ℝ))
      ((integrable_shock (t + 1)).smul (6 ^ (t + 1) : ℝ)) t,
    (iidSystem coin).E_smul (3 / 2 : ℝ) (xPath t) t,
    (iidSystem coin).E_smul (6 ^ (t + 1) : ℝ) (shock (t + 1)) t,
    E_shock_zero coin_mean t] with ω h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, hE]
  simp only [Pi.smul_apply, smul_eq_mul, h4, Pi.zero_apply, mul_zero, add_zero]

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420: at `σ = 1`, `β = 1/2`, `κ = 1/4`, `φ = 2`,
`φ_x = 0`, the process `(ĩ, r̃, x̃, π̃)` above solves the deviation system almost surely. -/
theorem devM_path : DevM (iidSystem coin) 1 (1 / 2) (1 / 4) 2 0 iPath rPath xPath piPath := by
  refine ⟨fun t => ⟨(integrable_piPath t).smul (2 : ℝ), ((integrable_piPath t).smul (2 : ℝ)).sub
    ((iidSystem coin).integrable_E _ _), integrable_xPath t, integrable_piPath t⟩,
    fun t => ⟨?_, ?_, ?_, ?_⟩⟩
  · refine Eventually.of_forall fun ω => ?_
    simp only [rPath, Pi.add_apply, Pi.sub_apply]
    ring
  · filter_upwards [E_xPath t] with ω h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rPath, iPath, h, E_piPath]
    simp only [piPath]
    ring
  · refine Eventually.of_forall fun ω => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, E_piPath]
    simp only [piPath]
    ring
  · refine Eventually.of_forall fun ω => ?_
    simp only [iPath, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero]

/-! ### Bounds on realised discounted output -/

/-- On a path of `±1` shocks, `|y_t| ≤ (3^{t+1} − 3)/2`. -/
theorem yPath_upper {ω : ℕ → ℝ} (hω : ∀ s, |shock s ω| = 1) (t : ℕ) :
    |yPath t ω| ≤ (3 ^ (t + 1) - 3) / 2 := by
  induction t with
  | zero => simp [yPath]
  | succ t ih =>
    simp only [yPath]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, hω (t + 1), abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
      abs_of_pos (by positivity : (0 : ℝ) < 3 ^ (t + 1)), mul_one, pow_succ 3 (t + 1)]
    have : 0 ≤ |yPath t ω| := abs_nonneg _
    nlinarith

/-- Cochrane (2023), p. 421: on a path of `±1` shocks realised discounted output explodes,
`|β^{t+1} x̃_{t+1}| = |y_{t+1}| ≥ (5/8) 3^{t+1}`. -/
theorem yPath_lower {ω : ℕ → ℝ} (hω : ∀ s, |shock s ω| = 1) (t : ℕ) :
    5 / 8 * 3 ^ (t + 1) ≤ |yPath (t + 1) ω| := by
  have hu := yPath_upper hω t
  have h3 : |3 ^ (t + 1) * shock (t + 1) ω| = 3 ^ (t + 1) := by
    rw [abs_mul, hω (t + 1), mul_one, abs_of_pos (by positivity)]
  have key := abs_sub_abs_le_abs_sub (3 ^ (t + 1) * shock (t + 1) ω) (-(3 / 4 * yPath t ω))
  simp only [yPath]
  rw [h3, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4), sub_neg_eq_add,
    add_comm (3 ^ (t + 1) * shock (t + 1) ω)] at key
  linarith

/-- Cochrane (2023), p. 421: realised discounted output `βᵗ x̃_t` is unbounded almost surely. -/
theorem realised_unbounded :
    ∀ᵐ ω ∂(iidSystem coin).μ, ¬ ∃ M, ∀ t, |(1 / 2 : ℝ) ^ t * xPath t ω| ≤ M := by
  filter_upwards [ae_all_iff.mpr shock_abs_one] with ω hω
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (8 / 5 * M)
  have h1 := hM (n + 1)
  have e : (1 / 2 : ℝ) ^ (n + 1) * xPath (n + 1) ω = yPath (n + 1) ω := by
    simp only [xPath, ← mul_assoc, ← mul_pow]
    norm_num
  rw [e] at h1
  have h2 := yPath_lower hω n
  have h3 : (n : ℝ) + 1 < 3 ^ (n + 1) := by
    have := Nat.lt_pow_self (by norm_num : 1 < 3) (n := n + 1)
    exact_mod_cast this
  linarith

/-- Cochrane (2023), p. 421: at `σ = 1`, `β = 1/2`, `κ = 1/4`, `φ = 2`, `φ_x = 0`, every deviation
on the coin space satisfies the real transversality condition in expectation,
`βʲ E_s x̃_{s+j} → 0`, at every date and almost every state. -/
theorem all_expected_tvc {i r x π : ℕ → (ℕ → ℝ) → ℝ}
    (h : DevM (iidSystem coin) 1 (1 / 2) (1 / 4) 2 0 i r x π) (s : ℕ) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      Tendsto (fun j => (1 / 2 : ℝ) ^ j * (iidSystem coin).E s (x (s + j)) ω) atTop (𝓝 0) := by
  filter_upwards [expected_pfDevX_ae (iidSystem coin) h s] with ω hω
  by_contra hn
  rcases (tvcX_fails_pf_iff one_pos (by norm_num) (by norm_num)).mp ⟨_, _, hω, hn⟩ with
    h1 | h1 | h1
  · norm_num at h1
  · rw [abs_of_pos (by norm_num)] at h1
    norm_num at h1
  · norm_num at h1

/-- **Pathwise real explosions under uncertainty** (Cochrane (2023), p. 421): on the i.i.d.
coin space at `σ = 1`, `β = 1/2`, `κ = 1/4`, `φ = 2`, `φ_x = 0`, the expected real
transversality condition holds for every deviation, at every date and almost every state, yet
a deviation exists whose realised discounted output is unbounded almost surely. -/
theorem pathwise_explosion :
    (∀ i r x π : ℕ → (ℕ → ℝ) → ℝ, DevM (iidSystem coin) 1 (1 / 2) (1 / 4) 2 0 i r x π →
      ∀ s, ∀ᵐ ω ∂(iidSystem coin).μ,
        Tendsto (fun j => (1 / 2 : ℝ) ^ j * (iidSystem coin).E s (x (s + j)) ω) atTop (𝓝 0)) ∧
      DevM (iidSystem coin) 1 (1 / 2) (1 / 4) 2 0 iPath rPath xPath piPath ∧
      ∀ᵐ ω ∂(iidSystem coin).μ, ¬ ∃ M, ∀ t, |(1 / 2 : ℝ) ^ t * xPath t ω| ≤ M :=
  ⟨fun _ _ _ _ h s => all_expected_tvc h s, devM_path, realised_unbounded⟩

end Cochrane.KeynesianStickyPrices.TidyR5PathwiseExplosion
