/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.FutureSales
import LongTermDebtDynamics.PolicyConstraints
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Expected future bond sales with random debt

Cochrane (2023), Online Appendix §A1.14, pp. 588–592, equations (1.63)–(1.68), and §7.3.3,
p. 224.

`FutureSales.x0Fun`, `FutureSales.hasDerivAt_x0` and `FutureSales.x1_formula` treat the expected
date-1 sale `F = B_1^{(2)} − B_0^{(2)}` as a number. Here the sale is a random variable known at
date 1 (a state-contingent sale), the date-0 positions `B_{−1}^{(j)}`, `B_0^{(j)}` are known at date
0, and surpluses are random. The sale is perturbed in a random direction `G` known at date 1:
`B_1^{(2)}(ε) = B_1^{(2)} + ε G` (`pertD`).

* `x0_eq_x0R`, `x0R_pull`: in every equilibrium of the three-period economy, `1/P_0` is the closed
  form (1.65)/(1.66) `x0R ε`, and with the date-0 quantities pulled out of `E_0`,
  `B_{−1}^{(0)} x0R ε = s_0 + A₁ E_0(β s_1 + β² s_2) + E_0(β² s_2 B_0^{(2)}(A₂ − A₁)/B_1^{(2)}(ε))`
  with `A_k = (B_0^{(k)} − B_{−1}^{(k)})/B_0^{(k)}`.
* `hasDerivAt_x0R`: **the derivative with random debt**,
  `d(1/P_0)/dε = β² B_0^{(2)} (A₁ − A₂) E_0(G s_2/(B_1^{(2)})²)/B_{−1}^{(0)}`, an exact `HasDerivAt`
  (the deterministic `FutureSales.hasDerivAt_x0` is the case `G = 1`, `s_2` known).
* `x0R_mono`, `x0R_strictMono`, `x0R_anti`, `x0R_const`: **the sign rule with random debt**: if
  the government sells proportionally more time-1 than time-2 debt at date 0 (`A₁ ≥ A₂`), larger
  state-contingent future sales (`G ≥ 0`) lower `P_0`; strictly under uniform bounds; the reverse
  for `A₁ ≤ A₂`; no effect at all when `A₁ = A₂`. The hypothesis `s_2 ≥ 0` is not an extra
  restriction: positive `P_2` requires `s_2 > 0` (`price_two_pos_iff`).
* `E_x1_eq_x1R`, `hasDerivAt_x1R`, `x1R_mono`: (1.64) with random sales: expected future sales
  raise `E_0(1/P_1)` (and the bond price `Q_0^{(1)}` with `P_0` fixed) when `B_0^{(2)} ≥ 0`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom

open Filter Topology MaturityStructure Asymptotics

/-- Cochrane (2023), Online Appendix p. 592: the derivative of `ε ↦ E_t(h/(u + εG))` at `0` is
`E_t(−hG/u²)`, for `u ≥ δ > 0`, `|G| ≤ Γ` and `|h| ≤ H` (the remainder is `O(ε²)` uniformly in
the state, so it passes through `E_t`). -/
theorem hasDerivAt_E_div {Ω : Type*} (𝔼 : ExpectationSystem Ω) {δ Γ H : ℝ} (hδ : 0 < δ)
    {u G h : Ω → ℝ} (hu : ∀ ω, δ ≤ u ω) (hG : ∀ ω, |G ω| ≤ Γ) (hh : ∀ ω, |h ω| ≤ H) (t : ℕ)
    (ω : Ω) :
    HasDerivAt (fun ε : ℝ => 𝔼.E t (h / (u + ε • G)) ω) (𝔼.E t (-(h * G) / u ^ 2) ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hΓ : 0 ≤ Γ := (abs_nonneg _).trans (hG ω)
  have hH : 0 ≤ H := (abs_nonneg _).trans (hh ω)
  set η : ℝ := δ / (2 * (Γ + 1)) with hη
  have hηpos : 0 < η := div_pos hδ (by linarith)
  have hηΓ : η * Γ ≤ δ / 2 := by
    rw [hη, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hbig : (fun e : ℝ => 𝔼.E t (h / (u + (0 + e) • G)) ω - 𝔼.E t (h / (u + (0 : ℝ) • G)) ω -
      e • 𝔼.E t (-(h * G) / u ^ 2) ω) =O[𝓝 0] (fun e : ℝ => e ^ 2) := by
    refine IsBigO.of_bound (2 * H * Γ ^ 2 / δ ^ 3) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hηpos] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have heΓ : |e| * Γ ≤ δ / 2 :=
      (mul_le_mul_of_nonneg_right he.le hΓ).trans hηΓ
    have hw : ∀ ω', δ / 2 ≤ u ω' + e * G ω' := fun ω' => by
      have h1 : |e * G ω'| ≤ δ / 2 := by
        rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (hG ω') (abs_nonneg e)).trans heΓ
      have := neg_abs_le (e * G ω')
      linarith [hu ω']
    have hfun : h / (u + (0 + e) • G) - h / (u + (0 : ℝ) • G) - e • (-(h * G) / u ^ 2) =
        fun ω' => h ω' * G ω' ^ 2 * e ^ 2 / (u ω' ^ 2 * (u ω' + e * G ω')) := by
      funext ω'
      have hv : 0 < u ω' := hδ.trans_le (hu ω')
      have hw' : 0 < u ω' + e * G ω' := (half_pos hδ).trans_le (hw ω')
      simp only [Pi.sub_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.neg_apply, Pi.mul_apply, Pi.pow_apply, zero_add, zero_mul, add_zero]
      field_simp
      ring
    have hval : 𝔼.E t (h / (u + (0 + e) • G)) ω - 𝔼.E t (h / (u + (0 : ℝ) • G)) ω -
        e • 𝔼.E t (-(h * G) / u ^ 2) ω =
        𝔼.E t (fun ω' => h ω' * G ω' ^ 2 * e ^ 2 / (u ω' ^ 2 * (u ω' + e * G ω'))) ω := by
      rw [← hfun, map_sub, map_sub, map_smul]
      rfl
    rw [hval, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hv : δ ≤ u ω' := hu ω'
    have hv0 : 0 < u ω' := hδ.trans_le hv
    have hw' := hw ω'
    have hden : δ ^ 2 * (δ / 2) ≤ u ω' ^ 2 * (u ω' + e * G ω') :=
      mul_le_mul (pow_le_pow_left₀ hδ.le hv 2) hw' (by positivity) (by positivity)
    have hG2 : G ω' ^ 2 ≤ Γ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hG ω') 2
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (G ω')),
      abs_of_nonneg (sq_nonneg e),
      abs_of_pos (mul_pos (pow_pos hv0 2) ((half_pos hδ).trans_le hw'))]
    calc |h ω'| * G ω' ^ 2 * e ^ 2 / (u ω' ^ 2 * (u ω' + e * G ω'))
        ≤ H * Γ ^ 2 * e ^ 2 / (δ ^ 2 * (δ / 2)) := by
          apply div_le_div₀ (by positivity) _ (by positivity) hden
          exact mul_le_mul_of_nonneg_right (mul_le_mul (hh ω') hG2 (sq_nonneg _) hH)
            (sq_nonneg e)
      _ = 2 * H * Γ ^ 2 / δ ^ 3 * e ^ 2 := by field_simp
  exact hbig.trans_isLittleO (isLittleO_pow_id (by norm_num))

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Online Appendix p. 589: the policy with the date-1 sale of time-2 debt
perturbed in the random direction `G`: `B_1^{(2)}(ε) = B_1^{(2)} + ε G`, all else unchanged. -/
noncomputable def pertD (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (ε : ℝ) : ℕ → ℕ → Ω → ℝ :=
  fun t m => if t = 2 ∧ m = 2 then D 2 2 + ε • G else D t m

/-- Cochrane (2023), Online Appendix p. 589: the perturbed time-2 debt. -/
theorem pertD_22 (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (ε : ℝ) :
    pertD D G ε 2 2 = D 2 2 + ε • G := by simp [pertD]

/-- Cochrane (2023), Online Appendix p. 589: the other positions are unchanged. -/
theorem pertD_ne (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (ε : ℝ) {t m : ℕ} (h : ¬ (t = 2 ∧ m = 2)) :
    pertD D G ε t m = D t m := by simp [pertD, h]

/-- Cochrane (2023), Online Appendix p. 589: with the direction `G` known at date 1, the perturbed
debt is predetermined whenever the original debt is. -/
theorem pertD_predetermined {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG : 𝔼.E 1 G = G) (ε : ℝ) : Predetermined 𝔼 (pertD D G ε) := by
  refine ⟨fun m => ?_, fun t m => ?_⟩
  · rw [pertD_ne D G ε (by omega)]; exact hD.1 m
  · by_cases h : t + 1 = 2 ∧ m = 2
    · obtain ⟨h1, rfl⟩ := h
      obtain rfl : t = 1 := by omega
      rw [pertD_22, map_add, map_smul, hD.2 1 2, hG]
    · rw [pertD_ne D G ε h]; exact hD.2 t m

/-- Cochrane (2023), Online Appendix eq. (1.65)/(1.66), pp. 590–591: the closed form for `1/P_0`
along the perturbation, with random debt. -/
noncomputable def x0R (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) :
    Ω → ℝ :=
  (s 0 + (D 1 1 - D 0 1) / D 1 1 *
      𝔼.E 0 (β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2)) +
    𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2))) / D 0 0

/-- Cochrane (2023), Online Appendix eqs. (1.63)–(1.66), pp. 589–591: **in every equilibrium of
the three-period economy with random debt**, `1/P_0 = x0R ε` (the flow conditions (7.1) at dates
0, 1, 2 with the perturbed policy). -/
theorem x0_eq_x0R (hpo : 𝔼.PullOut) {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hG : 𝔼.E 1 G = G)
    (hD3 : ∀ t j, D t (j + 3) = 0) (h0 : RealFlow 𝔼 β (pertD D G ε) x s 0)
    (h1 : RealFlow 𝔼 β (pertD D G ε) x s 1) (h2 : RealFlow 𝔼 β (pertD D G ε) x s 2)
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) (hD00 : ∀ ω, D 0 0 ω ≠ 0) :
    x 0 = x0R 𝔼 β D G s ε := by
  have hD3' : ∀ t j, pertD D G ε t (j + 3) = 0 := fun t j => by
    rw [pertD_ne D G ε (by omega)]; exact hD3 t j
  obtain ⟨F2, F1, F0⟩ := FutureSales.flows_of_realFlow 𝔼 hD3' h0 h1 h2
  have hp := pertD_predetermined 𝔼 hD hG ε
  have h22 : ∀ ω, pertD D G ε 2 2 ω ≠ 0 := fun ω => by
    rw [pertD_22]; simpa using hD22 ω
  have h11 : ∀ ω, pertD D G ε 1 1 ω ≠ 0 := fun ω => by
    rw [pertD_ne D G ε (by omega)]; exact hD11 ω
  have hz := FutureSales.price_zero 𝔼 hpo hp F2 F1 F0 h22 h11
  rw [pertD_22, pertD_ne D G ε (show ¬ (0 = 2 ∧ 0 = 2) by omega),
    pertD_ne D G ε (show ¬ (1 = 2 ∧ 1 = 2) by omega),
    pertD_ne D G ε (show ¬ (0 = 2 ∧ 1 = 2) by omega),
    pertD_ne D G ε (show ¬ (1 = 2 ∧ 2 = 2) by omega),
    pertD_ne D G ε (show ¬ (0 = 2 ∧ 2 = 2) by omega)] at hz
  funext ω
  have := congrFun hz ω
  simp only [Pi.mul_apply, Pi.add_apply] at this
  rw [x0R, Pi.div_apply, eq_div_iff (hD00 ω), mul_comm, this]
  rfl

/-- Cochrane (2023), Online Appendix p. 592: Cochrane's date-0 sale fractions
`A₁ = (B_0^{(1)} − B_{−1}^{(1)})/B_0^{(1)}`, `A₂ = (B_0^{(2)} − B_{−1}^{(2)})/B_0^{(2)}`, random but
known at date 0. -/
noncomputable def fracA (D : ℕ → ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ := (D 1 k - D 0 k) / D 1 k

/-- Cochrane (2023), Online Appendix p. 592: the coefficient of the dilution term,
`β² s_2 B_0^{(2)}(A₂ − A₁)`, written as `β² s_2 ((B_0^{(2)} − B_{−1}^{(2)}) − A₁ B_0^{(2)})`. -/
noncomputable def kCoef (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) : Ω → ℝ :=
  β ^ 2 • (s 2 * ((D 1 2 - D 0 2) - fracA D 1 * D 1 2))

/-- Cochrane (2023), Online Appendix eq. (1.66), p. 591, with the date-0 quantities pulled out of
`E_0`: `B_{−1}^{(0)} x0R ε = s_0 + A₁ E_0(β s_1 + β² s_2) + E_0(k/B_1^{(2)}(ε))` with
`k = β² s_2 B_0^{(2)}(A₂ − A₁)` (`kCoef`), whenever `B_1^{(2)}(ε) ≠ 0` in every state. -/
theorem x0R_pull (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) :
    x0R 𝔼 β D G s ε = (s 0 + fracA D 1 * 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) +
      𝔼.E 0 (kCoef β D s / (D 2 2 + ε • G))) / D 0 0 := by
  have hA1 : 𝔼.E 0 (fracA D 1) = fracA D 1 :=
    hdc 0 _ _ (by rw [map_sub, hD.2 0, hD.1]) (hD.2 0 1)
  have hsplit : β • s 1 + β ^ 2 • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2) =
      (β • s 1 + β ^ 2 • s 2) - β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G)) := by
    funext ω
    have := hD22 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.sub_apply]
    field_simp
    ring
  have hk : 𝔼.E 0 (β ^ 2 • ((D 1 2 - D 0 2) / (D 2 2 + ε • G) * s 2)) -
      fracA D 1 * 𝔼.E 0 (β ^ 2 • (D 1 2 * s 2 / (D 2 2 + ε • G))) =
      𝔼.E 0 (kCoef β D s / (D 2 2 + ε • G)) := by
    rw [← hpo 0 _ _ hA1, ← map_sub]
    congr 1
    funext ω
    have := hD22 ω
    simp only [kCoef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
      Pi.add_apply]
    field_simp
  rw [x0R]
  unfold fracA at hk ⊢
  rw [hsplit, map_sub, mul_sub, ← hk]
  congr 1
  ring

/-- Cochrane (2023), Online Appendix p. 592: `kCoef = β² s_2 B_0^{(2)} (A₂ − A₁)` when
`B_0^{(2)} ≠ 0`. -/
theorem kCoef_eq {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ} (h12 : ∀ ω, D 1 2 ω ≠ 0) :
    kCoef β D s = β ^ 2 • (s 2 * (D 1 2 * (fracA D 2 - fracA D 1))) := by
  funext ω
  have := h12 ω
  simp only [kCoef, fracA, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply,
    Pi.div_apply]
  field_simp

/-- Cochrane (2023), Online Appendix p. 592: **the derivative of `1/P_0` with respect to expected
future sales, with random debt.** For a state-contingent direction `G` known at date 1 with
`|G| ≤ Γ`, `B_1^{(2)} ≥ δ > 0`, `|s_2| ≤ H` and the date-0 positions bounded,
`d x0R/dε = β² B_0^{(2)} (A₁ − A₂) E_0(G s_2/(B_1^{(2)})²)/B_{−1}^{(0)}` at `ε = 0`. -/
theorem hasDerivAt_x0R (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β δ Γ K : ℝ} (hδ : 0 < δ) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hu : ∀ ω, δ ≤ D 2 2 ω) (hG : ∀ ω, |G ω| ≤ Γ)
    (hk : ∀ ω, |kCoef β D s ω| ≤ K) (h12 : ∀ ω, D 1 2 ω ≠ 0) (ω : Ω) :
    HasDerivAt (fun ε => x0R 𝔼 β D G s ε ω)
      (β ^ 2 * D 1 2 ω * (fracA D 1 ω - fracA D 2 ω) *
        𝔼.E 0 (G * s 2 / D 2 2 ^ 2) ω / D 0 0 ω) 0 := by
  have hΓ : 0 ≤ Γ := (abs_nonneg _).trans (hG ω)
  have hd := ((hasDerivAt_E_div 𝔼 hδ hu hG hk 0 ω).const_add
    (s 0 ω + fracA D 1 ω * 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) ω)).div_const (D 0 0 ω)
  have hηpos : 0 < δ / (2 * (Γ + 1)) := div_pos hδ (by linarith)
  have hev : (fun ε => x0R 𝔼 β D G s ε ω) =ᶠ[𝓝 0] fun ε =>
      (s 0 ω + fracA D 1 ω * 𝔼.E 0 (β • s 1 + β ^ 2 • s 2) ω +
        𝔼.E 0 (kCoef β D s / (D 2 2 + ε • G)) ω) / D 0 0 ω := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hηpos] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have hne : ∀ ω', D 2 2 ω' + e * G ω' ≠ 0 := fun ω' => by
      have h1 : |e * G ω'| ≤ δ / 2 := by
        rw [abs_mul]
        refine (mul_le_mul he.le (hG ω') (abs_nonneg _) hηpos.le).trans ?_
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
      have := neg_abs_le (e * G ω')
      have := hu ω'
      intro h0
      linarith
    rw [x0R_pull 𝔼 hpo hdc hD hne]
    rfl
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  have hA1 : 𝔼.E 0 (D 1 2 * (fracA D 1 - fracA D 2)) = D 1 2 * (fracA D 1 - fracA D 2) := by
    have k1 : 𝔼.E 0 (fracA D 1) = fracA D 1 :=
      hdc 0 _ _ (by rw [map_sub, hD.2 0, hD.1]) (hD.2 0 1)
    have k2 : 𝔼.E 0 (fracA D 2) = fracA D 2 :=
      hdc 0 _ _ (by rw [map_sub, hD.2 0, hD.1]) (hD.2 0 2)
    rw [hpo 0 _ _ (hD.2 0 2), map_sub, k1, k2]
  have hfun : -(kCoef β D s * G) / D 2 2 ^ 2 =
      β ^ 2 • ((D 1 2 * (fracA D 1 - fracA D 2)) * (G * s 2 / D 2 2 ^ 2)) := by
    rw [kCoef_eq h12]
    funext ω'
    simp only [Pi.neg_apply, Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply, Pi.pow_apply]
    ring
  rw [hfun, map_smul, hpo 0 _ _ hA1]
  simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), Online Appendix eq. (1.63), p. 589: with `B_1^{(2)} > 0`, the price level
`P_2 = B_1^{(2)}/s_2` is positive if and only if `s_2 > 0`; so in an equilibrium with positive
prices the time-2 surplus is positive in every state. -/
theorem price_two_pos_iff {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (F2 : D 2 2 * x 2 = s 2)
    (hD22 : ∀ ω, 0 < D 2 2 ω) (ω : Ω) : 0 < x 2 ω ↔ 0 < s 2 ω := by
  have := congrFun F2 ω
  simp only [Pi.mul_apply] at this
  rw [← this]
  exact ⟨fun h => mul_pos (hD22 ω) h, fun h => pos_of_mul_pos_right h (hD22 ω).le⟩

/-- Cochrane (2023), Online Appendix p. 592 (bullet), with random debt: **if the government sells
proportionally more time-1 than time-2 debt at date 0 (`A₁ ≥ A₂`, `B_0^{(2)} > 0`), larger
state-contingent future sales lower `P_0`**: for `G ≥ 0`, `s_2 ≥ 0`, `B_{−1}^{(0)} > 0`, `1/P_0` is
monotone in `ε` wherever `B_1^{(2)}(ε) > 0` in every state. -/
theorem x0R_mono (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 ≤ s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 2 ω ≤ fracA D 1 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε ≤ ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω ≤ x0R 𝔼 β D G s ε' ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0 ω]
  rw [x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos ω).ne'),
    x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos' ω).ne'), Pi.div_apply, Pi.div_apply]
  apply div_le_div_of_nonneg_right _ (hD00 ω).le
  simp only [Pi.add_apply]
  have hle : kCoef β D s / (D 2 2 + ε • G) ≤ kCoef β D s / (D 2 2 + ε' • G) := fun ω' => by
    have hk : kCoef β D s ω' ≤ 0 := by
      rw [kCoef_eq (fun ω => (h12 ω).ne')]
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg β) (mul_nonpos_of_nonneg_of_nonpos
        (hs2 ω') (mul_nonpos_of_nonneg_of_nonpos (h12 ω').le (by linarith [hA ω'])))
    simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_le_div_iff₀ (hpos ω') (hpos' ω')]
    nlinarith [mul_le_mul_of_nonneg_right hεε (hG0 ω')]
  linarith [𝔼.mono 0 hle ω]

/-- Cochrane (2023), Online Appendix p. 592: conversely, if `A₁ ≤ A₂`, larger state-contingent
future sales raise `P_0`: `1/P_0` is antitone in `ε`. -/
theorem x0R_anti (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε ε' : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 ≤ s 2 ω) (h12 : ∀ ω, 0 < D 1 2 ω)
    (hA : ∀ ω, fracA D 1 ω ≤ fracA D 2 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε ≤ ε') (ω : Ω) :
    x0R 𝔼 β D G s ε' ω ≤ x0R 𝔼 β D G s ε ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0 ω]
  rw [x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos ω).ne'),
    x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos' ω).ne'), Pi.div_apply, Pi.div_apply]
  apply div_le_div_of_nonneg_right _ (hD00 ω).le
  simp only [Pi.add_apply]
  have hle : kCoef β D s / (D 2 2 + ε' • G) ≤ kCoef β D s / (D 2 2 + ε • G) := fun ω' => by
    have hk : 0 ≤ kCoef β D s ω' := by
      rw [kCoef_eq (fun ω => (h12 ω).ne')]
      simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
      exact mul_nonneg (sq_nonneg β) (mul_nonneg (hs2 ω')
        (mul_nonneg (h12 ω').le (by linarith [hA ω'])))
    simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_le_div_iff₀ (hpos' ω') (hpos ω')]
    nlinarith [mul_le_mul_of_nonneg_right hεε (hG0 ω')]
  linarith [𝔼.mono 0 hle ω]

/-- Cochrane (2023), Online Appendix p. 592, with random debt: **when the two date-0 fractions
are equal (`A₁ = A₂`), expected future sales have no effect on `P_0` at all**, in any direction
`G` and for every `ε` with `B_1^{(2)}(ε) ≠ 0` in every state. -/
theorem x0R_const (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β ε : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (h12 : ∀ ω, D 1 2 ω ≠ 0) (hA : fracA D 1 = fracA D 2)
    (hne : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hne0 : ∀ ω, D 2 2 ω ≠ 0) :
    x0R 𝔼 β D G s ε = x0R 𝔼 β D G s 0 := by
  have hk : kCoef β D s = 0 := by
    rw [kCoef_eq h12, hA, sub_self]
    funext ω
    simp
  have hz : ∀ f : Ω → ℝ, (0 : Ω → ℝ) / f = 0 := fun f => funext fun ω => by simp
  rw [x0R_pull 𝔼 hpo hdc hD hne, x0R_pull 𝔼 hpo hdc hD (fun ω => by simpa using hne0 ω), hk,
    hz, hz]

/-- Cochrane (2023), Online Appendix p. 592 (bullet), with random debt, strict version: with
`A₁ − A₂ ≥ a > 0`, `B_0^{(2)} ≥ b > 0`, a direction `G ≥ γ > 0`, `s_2 ≥ σ > 0` and
`B_1^{(2)}(ε), B_1^{(2)}(ε') ≤ U`, larger future sales strictly lower `P_0`. -/
theorem x0R_strictMono (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β ε ε' a b γ σ U : ℝ} (hβ : β ≠ 0) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ) (hσ : 0 < σ)
    {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hG0 : ∀ ω, γ ≤ G ω) (hs2 : ∀ ω, σ ≤ s 2 ω) (h12 : ∀ ω, b ≤ D 1 2 ω)
    (hA : ∀ ω, a ≤ fracA D 1 ω - fracA D 2 ω) (hD00 : ∀ ω, 0 < D 0 0 ω)
    (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hU : ∀ ω, D 2 2 ω + ε' * G ω ≤ U)
    (hεε : ε < ε') (ω : Ω) :
    x0R 𝔼 β D G s ε ω < x0R 𝔼 β D G s ε' ω := by
  have hG0' : ∀ ω, 0 ≤ G ω := fun ω => hγ.le.trans (hG0 ω)
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0' ω]
  have h12' : ∀ ω, D 1 2 ω ≠ 0 := fun ω => (hb.trans_le (h12 ω)).ne'
  rw [x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos ω).ne'),
    x0R_pull 𝔼 hpo hdc hD (fun ω => (hpos' ω).ne'), Pi.div_apply, Pi.div_apply]
  apply div_lt_div_of_pos_right _ (hD00 ω)
  simp only [Pi.add_apply]
  set c : ℝ := β ^ 2 * σ * b * a * γ * (ε' - ε) / U ^ 2 with hc
  have hβ2 : 0 < β ^ 2 := by positivity
  have hU0 : 0 < U := (hpos' ω).trans_le (hU ω)
  have hcpos : 0 < c := by
    have : 0 < ε' - ε := by linarith
    positivity
  have hle : (fun _ => c) ≤ kCoef β D s / (D 2 2 + ε' • G) - kCoef β D s / (D 2 2 + ε • G) :=
    fun ω' => by
    rw [kCoef_eq h12']
    simp only [Pi.sub_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.mul_apply]
    have hp := hpos ω'
    have hp' := hpos' ω'
    have hu' := hU ω'
    have hu : D 2 2 ω' + ε * G ω' ≤ U := by nlinarith [hG0' ω']
    set q : ℝ := β ^ 2 * (s 2 ω' * (D 1 2 ω' * (fracA D 1 ω' - fracA D 2 ω'))) with hq
    have hq0 : β ^ 2 * σ * b * a ≤ q := by
      rw [hq]
      have h1 : σ * (b * a) ≤ s 2 ω' * (D 1 2 ω' * (fracA D 1 ω' - fracA D 2 ω')) :=
        mul_le_mul (hs2 ω') (mul_le_mul (h12 ω') (hA ω') ha.le (hb.le.trans (h12 ω')))
          (by positivity) (hσ.le.trans (hs2 ω'))
      nlinarith
    have hkey : β ^ 2 * (s 2 ω' * (D 1 2 ω' * (fracA D 2 ω' - fracA D 1 ω'))) /
        (D 2 2 ω' + ε' * G ω') - β ^ 2 * (s 2 ω' * (D 1 2 ω' * (fracA D 2 ω' - fracA D 1 ω'))) /
        (D 2 2 ω' + ε * G ω') = q * ((ε' - ε) * G ω') /
          ((D 2 2 ω' + ε * G ω') * (D 2 2 ω' + ε' * G ω')) := by
      rw [hq, div_sub_div _ _ hp'.ne' hp.ne', div_eq_div_iff (mul_ne_zero hp'.ne' hp.ne')
        (mul_ne_zero hp.ne' hp'.ne')]
      ring
    rw [hkey, hc]
    have hden : (D 2 2 ω' + ε * G ω') * (D 2 2 ω' + ε' * G ω') ≤ U ^ 2 := by
      rw [sq]; exact mul_le_mul hu hu' hp'.le hU0.le
    have hnum : β ^ 2 * σ * b * a * (γ * (ε' - ε)) ≤ q * ((ε' - ε) * G ω') := by
      have : γ * (ε' - ε) ≤ (ε' - ε) * G ω' := by nlinarith [hG0 ω']
      exact mul_le_mul hq0 this (by nlinarith)
        ((by positivity : (0 : ℝ) ≤ β ^ 2 * σ * b * a).trans hq0)
    rw [show β ^ 2 * σ * b * a * γ * (ε' - ε) / U ^ 2 =
      β ^ 2 * σ * b * a * (γ * (ε' - ε)) / U ^ 2 by ring]
    exact div_le_div₀ ((by positivity : (0 : ℝ) ≤ β ^ 2 * σ * b * a * (γ * (ε' - ε))).trans hnum)
      hnum (by positivity) hden
  have := 𝔼.mono 0 hle ω
  rw [𝔼.const, map_sub, Pi.sub_apply] at this
  linarith

/-! ### (1.64): the expected price level at date 1 -/

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: `E_0(1/P_1)` along the perturbation,
`E_0[s_1 + β ((B_1^{(2)}(ε) − B_0^{(2)})/B_1^{(2)}(ε)) s_2] / B_0^{(1)}`. -/
noncomputable def x1R (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (G : Ω → ℝ) (s : ℕ → Ω → ℝ) (ε : ℝ) :
    Ω → ℝ :=
  𝔼.E 0 (s 1 + β • ((D 2 2 + ε • G - D 1 2) / (D 2 2 + ε • G) * s 2)) / D 1 1

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590: in every equilibrium of the three-period
economy with random debt, `E_0(1/P_1) = x1R ε`. -/
theorem E_x1_eq_x1R (hpo : 𝔼.PullOut) {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hG : 𝔼.E 1 G = G)
    (hD3 : ∀ t j, D t (j + 3) = 0) (h0 : RealFlow 𝔼 β (pertD D G ε) x s 0)
    (h1 : RealFlow 𝔼 β (pertD D G ε) x s 1) (h2 : RealFlow 𝔼 β (pertD D G ε) x s 2)
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) (hD11 : ∀ ω, D 1 1 ω ≠ 0) :
    𝔼.E 0 (x 1) = x1R 𝔼 β D G s ε := by
  have hD3' : ∀ t j, pertD D G ε t (j + 3) = 0 := fun t j => by
    rw [pertD_ne D G ε (by omega)]; exact hD3 t j
  obtain ⟨F2, F1, -⟩ := FutureSales.flows_of_realFlow 𝔼 hD3' h0 h1 h2
  have hp := pertD_predetermined 𝔼 hD hG ε
  have h22 : ∀ ω, pertD D G ε 2 2 ω ≠ 0 := fun ω => by
    rw [pertD_22]; simpa using hD22 ω
  have hz := FutureSales.E_price_one 𝔼 hpo hp F2 F1 h22
  rw [pertD_22, pertD_ne D G ε (show ¬ (1 = 2 ∧ 1 = 2) by omega),
    pertD_ne D G ε (show ¬ (1 = 2 ∧ 2 = 2) by omega)] at hz
  funext ω
  have := congrFun hz ω
  simp only [Pi.mul_apply] at this
  rw [x1R, Pi.div_apply, eq_div_iff (hD11 ω), mul_comm, this]

/-- Cochrane (2023), Online Appendix eq. (1.64), p. 590, split: `x1R ε =
(E_0(s_1 + β s_2) − E_0(β B_0^{(2)} s_2/B_1^{(2)}(ε)))/B_0^{(1)}` when `B_1^{(2)}(ε) ≠ 0`. -/
theorem x1R_split {β ε : ℝ} {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD22 : ∀ ω, D 2 2 ω + ε * G ω ≠ 0) :
    x1R 𝔼 β D G s ε = (𝔼.E 0 (s 1 + β • s 2) -
      𝔼.E 0 (β • (D 1 2 * s 2) / (D 2 2 + ε • G))) / D 1 1 := by
  rw [x1R, ← map_sub]
  congr 2
  funext ω
  have := hD22 ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.div_apply,
    Pi.sub_apply]
  field_simp
  ring

/-- Cochrane (2023), Online Appendix p. 591 (bullet), with random debt: the derivative of
`E_0(1/P_1)` with respect to expected future sales in a state-contingent direction `G`,
`β E_0(B_0^{(2)} G s_2/(B_1^{(2)})²)/B_0^{(1)}` (exact `HasDerivAt`, `B_1^{(2)} ≥ δ > 0`). -/
theorem hasDerivAt_x1R {β δ Γ H : ℝ} (hδ : 0 < δ) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hu : ∀ ω, δ ≤ D 2 2 ω) (hG : ∀ ω, |G ω| ≤ Γ)
    (hh : ∀ ω, |(β • (D 1 2 * s 2)) ω| ≤ H) (ω : Ω) :
    HasDerivAt (fun ε => x1R 𝔼 β D G s ε ω)
      (𝔼.E 0 (β • (D 1 2 * G * s 2 / D 2 2 ^ 2)) ω / D 1 1 ω) 0 := by
  have hΓ : 0 ≤ Γ := (abs_nonneg _).trans (hG ω)
  have hd := ((hasDerivAt_E_div 𝔼 hδ hu hG hh 0 ω).const_sub
    (𝔼.E 0 (s 1 + β • s 2) ω)).div_const (D 1 1 ω)
  have hηpos : 0 < δ / (2 * (Γ + 1)) := div_pos hδ (by linarith)
  have hev : (fun ε => x1R 𝔼 β D G s ε ω) =ᶠ[𝓝 0] fun ε =>
      (𝔼.E 0 (s 1 + β • s 2) ω - 𝔼.E 0 (β • (D 1 2 * s 2) / (D 2 2 + ε • G)) ω) / D 1 1 ω := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hηpos] with e he
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at he
    have hne : ∀ ω', D 2 2 ω' + e * G ω' ≠ 0 := fun ω' => by
      have h1 : |e * G ω'| ≤ δ / 2 := by
        rw [abs_mul]
        refine (mul_le_mul he.le (hG ω') (abs_nonneg _) hηpos.le).trans ?_
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
      have := neg_abs_le (e * G ω')
      have := hu ω'
      intro h0
      linarith
    rw [x1R_split 𝔼 hne]
    rfl
  refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
  have hfun : -(β • (D 1 2 * s 2) * G) / D 2 2 ^ 2 = -(β • (D 1 2 * G * s 2 / D 2 2 ^ 2)) := by
    funext ω'
    simp only [Pi.neg_apply, Pi.mul_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul,
      Pi.pow_apply]
    ring
  rw [hfun, map_neg, Pi.neg_apply]
  ring

/-- Cochrane (2023), Online Appendix p. 591 (bullet), with random debt: **if the government has
sold time-2 debt at date 0 (`B_0^{(2)} ≥ 0`), larger state-contingent future sales (`G ≥ 0`)
raise `E_0(1/P_1)`**, and so the bond price `Q_0^{(1)} = β P_0 E_0(1/P_1)` with `P_0` fixed
(`s_2 ≥ 0`, `β ≥ 0`, `B_0^{(1)} > 0`, `B_1^{(2)}(ε) > 0`). -/
theorem x1R_mono {β ε ε' : ℝ} (hβ : 0 ≤ β) {D : ℕ → ℕ → Ω → ℝ} {G : Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hG0 : ∀ ω, 0 ≤ G ω) (hs2 : ∀ ω, 0 ≤ s 2 ω) (h12 : ∀ ω, 0 ≤ D 1 2 ω)
    (hD11 : ∀ ω, 0 < D 1 1 ω) (hpos : ∀ ω, 0 < D 2 2 ω + ε * G ω) (hεε : ε ≤ ε') (ω : Ω) :
    x1R 𝔼 β D G s ε ω ≤ x1R 𝔼 β D G s ε' ω := by
  have hpos' : ∀ ω, 0 < D 2 2 ω + ε' * G ω := fun ω => by
    nlinarith [hpos ω, hG0 ω]
  rw [x1R_split 𝔼 (fun ω => (hpos ω).ne'), x1R_split 𝔼 (fun ω => (hpos' ω).ne'),
    Pi.div_apply, Pi.div_apply]
  apply div_le_div_of_nonneg_right _ (hD11 ω).le
  have hle : β • (D 1 2 * s 2) / (D 2 2 + ε' • G) ≤ β • (D 1 2 * s 2) / (D 2 2 + ε • G) :=
    fun ω' => by
    simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply]
    have hk : 0 ≤ β * (D 1 2 ω' * s 2 ω') := mul_nonneg hβ (mul_nonneg (h12 ω') (hs2 ω'))
    rw [div_le_div_iff₀ (hpos' ω') (hpos ω')]
    nlinarith [mul_le_mul_of_nonneg_right hεε (hG0 ω')]
  simp only [Pi.sub_apply]
  linarith [𝔼.mono 0 hle ω]

end Cochrane.LongTermDebtDynamics.TidyR5FutureSalesRandom
