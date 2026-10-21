/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.AR1Responses
import KeynesianStickyPrices.ExpectationsFiniteTree
import KeynesianStickyPrices.FullModel

/-!
# Persistence does not determine the sign of the inflation response

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.3.1, pp. 405–406
(eq. (17.14)), §17.4.1, p. 410, and §17.4.3, p. 416.

* (17.14): an inflation target and an interest-rate target are an equilibrium pair of the
  simple model iff `i*_t = (1 + 1/(σκ)) E_t π*_{t+1} − π*_t/(σκ)` (`eq_17_14`).
* The printed inverse of (17.14), `E_t π*_{t+1} = σκ/(1+σκ) ∑ (1+σκ)^{−j} i*_{t−j}`, omits past
  expectational errors (survey error **E8**, confirmed): the correct statement adds
  `∑_{j ≥ 1} (1+σκ)^{−j} δ_{t+1−j}` (`corrected_inverse`); the printed form holds iff the
  error term vanishes, e.g. with no past surprises (`printed_inverse_of_no_surprise`), and fails
  for the dashed equilibria of Figure 17.2 (`printed_inverse_false`).
* "Any value of unexpected inflation is consistent with any persistence of the interest-rate
  target": for every expectation system with a date-1 news shock `ε`, every bounded path `g` of
  the rate target and every `c`, there is a bounded equilibrium with `ΔE_1 π*_1 = c ε`
  (`any_sign`); under genuine uncertainty on the coin-flip tree (`any_sign_coin`); a permanent
  rise with a negative response (`permanent_negative`) and a one-period rise with a positive
  response (`transitory_positive`).
* "The long-run response of inflation to interest rates … is always positive": in every
  equilibrium in which the rate converges and expectational errors die out, inflation
  converges to the rate (`long_run_one`, using `SharedTools.tendsto_zero_of_stable`), in
  particular after an announcement (`any_sign_long_run`).
* The full model (17.18) under perfect foresight after the announcement (§17.4.1, p. 410;
  §17.4.3, p. 416), in the notation of `FullModel` (`FullModel.Second`, `FullModel.path`): for
  every bounded rate path and every value `c` of announcement-date inflation there is exactly
  one bounded equilibrium (`full_any_sign`), namely `FullModel.path` with `π_0 = c`, and
  inflation converges to the rate in the long run (`full_long_run`). The stable root of the
  dynamics is the open-mouth persistence: `η* = 1/λ₁` (`etaStar_eq_inv_lam1`), and the unstable
  root of `βλ² − (1+β+σκ)λ + 1` is `1/λ₂ > 1` (`etaStar_mul_inv_lam2`, `one_lt_inv_lam2`).
-/

namespace Cochrane.KeynesianStickyPrices.PersistenceFreedom

open Filter Topology StaticIS AR1Responses
open SharedTools (tendsto_zero_of_stable tendsto_of_stable_avg eq_backward_series)

variable {Ω : Type*}

/-! ### (17.14) and its inverse -/

/-- Cochrane (2023), eq. (17.14), p. 405: a target pair `(i*, π*)` is an equilibrium of the
simple model (17.7) iff `i*_t = (1 + 1/(σκ)) E_t π*_{t+1} − π*_t/(σκ)`. -/
theorem eq_17_14 (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (hσκ : σ * κ ≠ 0)
    (istar πstar : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ istar πstar ↔ 𝔼.Adapted πstar ∧ ∀ t ω,
      istar t ω = (1 + 1 / (σ * κ)) * 𝔼.E t (πstar (t + 1)) ω - πstar t ω / (σ * κ) := by
  have hσ := left_ne_zero_of_mul hσκ
  have hκ := right_ne_zero_of_mul hσκ
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun ω => ?_)
  constructor
  · intro e; field_simp; linear_combination e
  · intro e; field_simp at e; linear_combination e

/-- Cochrane (2023), eq. (17.14), p. 405 (survey error E8, corrected inverse): on the integers
(an infinite past), if `e_t = E_t π_{t+1}` satisfies (17.7), `e_t = π_t/(1+σκ) + σκ/(1+σκ) i_t`,
and `e`, `π`, `i` are bounded, then with the expectational errors `δ_s = π_s − e_{s−1}`,
`e_t = σκ/(1+σκ) ∑_{j≥0} (1+σκ)^{−j} i_{t−j} + ∑_{j≥0} (1+σκ)^{−(j+1)} δ_{t−j}`. The
statement is pathwise (one history at a time). -/
theorem corrected_inverse {σ κ Me Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {e π i : ℤ → ℝ}
    (he : ∀ s, |e s| ≤ Me) (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi)
    (h : ∀ s, e s = 1 / (1 + σ * κ) * π s + σ * κ / (1 + σ * κ) * i s) (t : ℤ) :
    e t = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) +
      ∑' j : ℕ, (1 / (1 + σ * κ)) ^ (j + 1) * (π (t - j) - e (t - j - 1)) := by
  obtain ⟨ha0, ha1, hb0, -⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  have haa : |a| < 1 := by rw [abs_of_pos ha0]; exact ha1
  set w : ℤ → ℝ := fun s => b * i s + a * (π s - e (s - 1)) with hw
  have hwb : ∀ s, |w s| ≤ b * |Mi| + a * (|Mπ| + |Me|) := fun s => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos hb0]
      exact mul_le_mul_of_nonneg_left ((hi _).trans (le_abs_self _)) hb0.le
    · rw [abs_mul, abs_of_pos ha0]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_)) ha0.le
      · exact (hπ _).trans (le_abs_self _)
      · exact (he _).trans (le_abs_self _)
  have hrec : ∀ s, e (s + 1) = a * e s + w (s + 1) := fun s => by
    rw [h (s + 1), hw]; simp only [add_sub_cancel_right]; ring
  rw [eq_backward_series haa he hwb hrec t]
  have hg := summable_geometric_of_lt_one (abs_nonneg a) haa
  have hsi : Summable fun j : ℕ => a ^ j * i (t - j) :=
    Summable.of_norm_bounded (hg.mul_right Mi) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg (abs_nonneg a) j)
  have hsd : Summable fun j : ℕ => a ^ (j + 1) * (π (t - j) - e (t - j - 1)) :=
    Summable.of_norm_bounded ((hg.mul_left |a|).mul_right (Mπ + Me)) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, pow_succ, mul_comm (|a| ^ j) |a|]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hπ _) (he _)))
        (by positivity)
  rw [← tsum_mul_left, ← (hsi.mul_left b).tsum_add hsd]
  refine tsum_congr fun j => ?_
  rw [hw]
  ring

/-- Cochrane (2023), eq. (17.14), p. 405: the printed inverse
`E_t π*_{t+1} = σκ/(1+σκ) ∑ (1+σκ)^{−j} i*_{t−j}` holds when there have been no expectational
errors up to date `t` (`π_s = E_{s−1} π_s` for `s ≤ t`). -/
theorem printed_inverse_of_no_surprise {σ κ Me Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {e π i : ℤ → ℝ}
    (he : ∀ s, |e s| ≤ Me) (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi)
    (h : ∀ s, e s = 1 / (1 + σ * κ) * π s + σ * κ / (1 + σ * κ) * i s) {t : ℤ}
    (hns : ∀ s ≤ t, π s = e (s - 1)) :
    e t = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) := by
  rw [corrected_inverse hσκ he hπ hi h t]
  have : ∀ j : ℕ, (1 / (1 + σ * κ)) ^ (j + 1) * (π (t - j) - e (t - j - 1)) = 0 := fun j => by
    rw [hns (t - j) (by omega), sub_self, mul_zero]
  rw [tsum_congr this, tsum_zero, add_zero]

/-- Cochrane (2023), eq. (17.14), p. 405, survey error E8: the printed inverse is false in
general. With `σκ = 1` (so the coefficient is `1/2`), `i* = 0` and a single unexpected
inflation `δ_1 = 1` (the dashed lines of Figure 17.2), `e_t = E_t π_{t+1}` and `π` satisfy
(17.7), all are bounded, yet `e_1 = 1/2` while the printed formula gives 0. -/
theorem printed_inverse_false :
    ∃ e π i : ℤ → ℝ, (∀ s, |e s| ≤ 1) ∧ (∀ s, |π s| ≤ 1) ∧ (∀ s, |i s| ≤ 1) ∧
      (∀ s, e s = 1 / (1 + 1) * π s + 1 / (1 + 1) * i s) ∧
      e 1 ≠ 1 / (1 + 1) * ∑' j : ℕ, (1 / (1 + 1 : ℝ)) ^ j * i (1 - j) := by
  refine ⟨fun s => if 0 < s then (1 / 2 : ℝ) ^ s.toNat else 0,
    fun s => if 0 < s then (1 / 2 : ℝ) ^ (s.toNat - 1) else 0, fun _ => 0,
    fun s => ?_, fun s => ?_, fun s => by simp, fun s => ?_, ?_⟩
  · dsimp only
    split_ifs
    · rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp
  · dsimp only
    split_ifs
    · rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp
  · dsimp only
    split_ifs with hs
    · have hn : s.toNat = s.toNat - 1 + 1 := by omega
      rw [hn, pow_succ, Nat.add_sub_cancel]
      ring
    · simp
  · simp

/-! ### Any persistence with any sign (§17.3.1, p. 405) -/

/-- Cochrane (2023), p. 405: the inflation response (per unit of the date-1 news shock) after an
announcement at date 1: `p_0 = 0`, announcement-date inflation `p_1 = c`, and thereafter
`p_{t+1} = p_t/(1+σκ) + σκ/(1+σκ) g_t`. -/
noncomputable def targetPath (σ κ : ℝ) (g : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => c
  | t + 2 => 1 / (1 + σ * κ) * targetPath σ κ g c (t + 1) + σ * κ / (1 + σ * κ) * g (t + 1)

/-- Cochrane (2023), p. 405: the interest-rate target `i*_t = g_t ε` for `t ≥ 1` (zero before
the news). -/
noncomputable def shockRate (g : ℕ → ℝ) (ε : Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (if t = 0 then 0 else g t) * ε ω

/-- Cochrane (2023), p. 405: the inflation target `π*_t = p_t ε`. -/
noncomputable def shockInfl (p : ℕ → ℝ) (ε : Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω => p t * ε ω

/-- Cochrane (2023), p. 405: the response path is bounded when `g` is. -/
theorem targetPath_bounded {σ κ M : ℝ} (hσκ : 0 < σ * κ) {g : ℕ → ℝ} (hg : ∀ t, |g t| ≤ M)
    (c : ℝ) : ∀ t, |targetPath σ κ g c t| ≤ |c| + |M| / (1 - 1 / (1 + σ * κ)) := by
  obtain ⟨ha0, ha1, hb0, hab⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  set K := |c| + |M| / (1 - a) with hK
  have h1a : 0 < 1 - a := by linarith
  have hKa : (1 - a) * K = (1 - a) * |c| + |M| := by rw [hK]; field_simp
  have hK0 : |c| ≤ K := by have : 0 ≤ |M| / (1 - a) := by positivity
                           linarith
  have hstep : ∀ x : ℝ, |x| ≤ K → ∀ t, |a * x + b * g t| ≤ K := fun x hx t => by
    have e1 : |a * x| ≤ a * K := by
      rw [abs_mul, abs_of_pos ha0]; exact mul_le_mul_of_nonneg_left hx ha0.le
    have e2 : |b * g t| ≤ |M| := by
      rw [abs_mul, abs_of_pos hb0]
      calc b * |g t| ≤ 1 * |g t| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ ≤ |M| := by rw [one_mul]; exact (hg t).trans (le_abs_self _)
    have hc : 0 ≤ (1 - a) * |c| := mul_nonneg h1a.le (abs_nonneg _)
    linarith [abs_add_le (a * x) (b * g t)]
  have key : ∀ t, |targetPath σ κ g c t| ≤ K ∧ |targetPath σ κ g c (t + 1)| ≤ K := by
    intro t
    induction t with
    | zero => exact ⟨by simp only [targetPath, abs_zero]; positivity, hK0⟩
    | succ t ih => exact ⟨ih.2, hstep _ ih.2 (t + 1)⟩
  exact fun t => (key t).1

/-- Cochrane (2023), p. 405, "Any value of unexpected inflation is consistent with any
persistence of the interest-rate target": let `ε` be news revealed at date 1 (`E_0 ε = 0`,
`E_1 ε = ε`). For every bounded target path `g` (any persistence) and every `c`, the pair
`i*_t = g_t ε` (`t ≥ 1`), `π*_t = p_t ε` is a bounded equilibrium of (17.7) — so (17.14) holds —
with unexpected inflation `ΔE_1 π*_1 = π*_1 − E_0 π*_1 = c ε`. -/
theorem any_sign (𝔼 : ExpectationSystem Ω) {σ κ Mg Mε : ℝ} (hσκ : 0 < σ * κ) {ε : Ω → ℝ}
    (hε0 : 𝔼.E 0 ε = 0) (hε1 : 𝔼.E 1 ε = ε) (hεb : ∀ ω, |ε ω| ≤ Mε) {g : ℕ → ℝ}
    (hg : ∀ t, |g t| ≤ Mg) (c : ℝ) :
    REModel 𝔼 σ κ (shockRate g ε) (shockInfl (targetPath σ κ g c) ε) ∧
      BoundedProc (shockInfl (targetPath σ κ g c) ε) ∧
      BoundedProc (shockRate g ε) ∧
      shockInfl (targetPath σ κ g c) ε 1 - 𝔼.E 0 (shockInfl (targetPath σ κ g c) ε 1) =
        c • ε := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have hεt : ∀ t, 1 ≤ t → 𝔼.E t ε = ε := fun t ht => by
    rw [← hε1, 𝔼.known ht]
  have hEs : ∀ t (q : ℝ), 𝔼.E t (fun ω => q * ε ω) = fun ω => q * 𝔼.E t ε ω := fun t q => by
    have := 𝔼.E_smul t q ε
    exact this
  set p := targetPath σ κ g c
  refine ⟨⟨fun t => ?_, fun t ω => ?_⟩,
    ⟨(|c| + |Mg| / (1 - 1 / (1 + σ * κ))) * Mε, fun t ω => ?_⟩, ⟨|Mg| * Mε, fun t ω => ?_⟩, ?_⟩
  · cases t with
    | zero =>
      change 𝔼.E 0 (fun ω => p 0 * ε ω) = fun ω => p 0 * ε ω
      rw [hEs]; simp [p, targetPath]
    | succ t =>
      change 𝔼.E (t + 1) (fun ω => p (t + 1) * ε ω) = fun ω => p (t + 1) * ε ω
      rw [hEs, hεt (t + 1) (Nat.le_add_left 1 t)]
  · change p t * ε ω = -(σ * κ) * ((if t = 0 then 0 else g t) * ε ω) +
      (1 + σ * κ) * 𝔼.E t (fun ω => p (t + 1) * ε ω) ω
    rw [hEs]
    cases t with
    | zero => simp [p, targetPath, hε0]
    | succ t =>
      rw [hεt (t + 1) (Nat.le_add_left 1 t)]
      simp only [Nat.add_one_ne_zero, ↓reduceIte, p, targetPath]
      field_simp
      ring
  · rw [show shockInfl p ε t ω = p t * ε ω from rfl, abs_mul]
    exact mul_le_mul (targetPath_bounded hσκ hg c t) (hεb ω) (abs_nonneg _)
      ((abs_nonneg _).trans (targetPath_bounded hσκ hg c t))
  · rw [show shockRate g ε t ω = (if t = 0 then 0 else g t) * ε ω from rfl, abs_mul]
    refine mul_le_mul ?_ (hεb ω) (abs_nonneg _) (abs_nonneg Mg)
    split_ifs
    · simp
    · exact (hg t).trans (le_abs_self _)
  · funext ω
    change p 1 * ε ω - 𝔼.E 0 (fun ω => p 1 * ε ω) ω = c * ε ω
    rw [hEs, hε0]
    simp [p, targetPath]

/-- Cochrane (2023), p. 406, "The long-run response of inflation to interest rates in this model
is always positive": after the announcement, if the rate target converges, `g_t → ḡ`, the
inflation response converges to `ḡ`, whatever the announcement-date jump `c`. -/
theorem any_sign_long_run {σ κ gb : ℝ} (hσκ : 0 < σ * κ) {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 gb)) (c : ℝ) :
    Tendsto (targetPath σ κ g c) atTop (𝓝 gb) := by
  obtain ⟨ha0, ha1, -, hab⟩ := coeff_17_7 hσκ
  have haa : |1 / (1 + σ * κ)| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have := tendsto_of_stable_avg haa hab (x := fun n => targetPath σ κ g c (n + 1))
    (y := fun n => g (n + 1)) (fun n => rfl) ((tendsto_add_atTop_iff_nat 1).mpr hg)
  exact (tendsto_add_atTop_iff_nat 1).mp this

/-- Cochrane (2023), p. 405 and Figure 17.2 ("a permanent `i*_t` shock can come with a negative
`π*_t` response"): a permanent rise `g ≡ 1` with `c = −1`: inflation falls on announcement and
then rises to the new rate. -/
theorem permanent_negative {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    targetPath σ κ (fun _ => 1) (-1) 1 < 0 ∧
      Tendsto (targetPath σ κ (fun _ => 1) (-1)) atTop (𝓝 1) :=
  ⟨by simp [targetPath], any_sign_long_run hσκ tendsto_const_nhds (-1)⟩

/-- Cochrane (2023), p. 405 ("Contrary examples, with transitory interest rates … and positive
inflation responses are just as easy to construct"): a one-period rate rise (`g_1 = 1`, zero
otherwise) with `c = 1`, a positive inflation response that dies out. -/
theorem transitory_positive {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    0 < targetPath σ κ (fun t => if t = 1 then 1 else 0) 1 1 ∧
      Tendsto (targetPath σ κ (fun t => if t = 1 then 1 else 0) 1) atTop (𝓝 0) := by
  refine ⟨by simp [targetPath], any_sign_long_run hσκ ?_ 1⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with t ht
  simp [ht.ne']

/-- Cochrane (2023), p. 405, under genuine uncertainty: on the coin-flip tree (news revealed by
the first flip at date 1) every bounded persistence pattern `g` of the rate target is compatible
with every value `c` of unexpected inflation on the announcement date (per unit of the shock,
which is `+1` in the heads state). -/
theorem any_sign_coin {σ κ Mg : ℝ} (hσκ : 0 < σ * κ) {g : ℕ → ℝ} (hg : ∀ t, |g t| ≤ Mg)
    (c : ℝ) :
    ∃ istar πstar : ℕ → Bool × Bool → ℝ,
      REModel ExpectationsFiniteTree.coinSystem σ κ istar πstar ∧ BoundedProc πstar ∧
      BoundedProc istar ∧
      πstar 1 (true, true) - ExpectationsFiniteTree.coinSystem.E 0 (πstar 1) (true, true) = c ∧
      ∀ t, 1 ≤ t → istar t (true, true) = g t := by
  have hε : ExpectationsFiniteTree.coinShock 1 = ExpectationsFiniteTree.coinAR1 0 1 := by
    funext ω; simp [ExpectationsFiniteTree.coinAR1]
  have hε0 : ExpectationsFiniteTree.coinSystem.E 0 (ExpectationsFiniteTree.coinShock 1) = 0 :=
    ExpectationsFiniteTree.coinShock_mean_zero 0
  have hε1 : ExpectationsFiniteTree.coinSystem.E 1 (ExpectationsFiniteTree.coinShock 1) =
      ExpectationsFiniteTree.coinShock 1 := by
    rw [hε]; exact (ExpectationsFiniteTree.coinAR1_isAR1 0).1 1
  have hεb : ∀ ω, |ExpectationsFiniteTree.coinShock 1 ω| ≤ 1 := fun ω => by
    unfold ExpectationsFiniteTree.coinShock; split_ifs <;> simp
  obtain ⟨hm, hb, hbi, hd⟩ := any_sign ExpectationsFiniteTree.coinSystem hσκ hε0 hε1 hεb hg c
  refine ⟨_, _, hm, hb, hbi, ?_, fun t ht => ?_⟩
  · have := congrFun hd (true, true)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]; simp [ExpectationsFiniteTree.coinShock]
  · simp [shockRate, ExpectationsFiniteTree.coinShock, show t ≠ 0 by omega]

/-- Cochrane (2023), p. 406, "A persistently high interest rate still drives inflation up
eventually in all equilibria of this model": in any equilibrium of (17.7), along any history in
which the rate converges to `ī` and the expectational errors die out, inflation converges to
`ī`. -/
theorem long_run_one {𝔼 : ExpectationSystem Ω} {σ κ ib : ℝ} (hσκ : 0 < σ * κ)
    {i π : ℕ → Ω → ℝ} (hπ : REModel 𝔼 σ κ i π) {ω : Ω}
    (hi : Tendsto (fun t => i t ω) atTop (𝓝 ib))
    (hδ : Tendsto (fun t => π (t + 1) ω - 𝔼.E t (π (t + 1)) ω) atTop (𝓝 0)) :
    Tendsto (fun t => π t ω) atTop (𝓝 ib) := by
  obtain ⟨ha0, ha1, -, hab⟩ := coeff_17_7 hσκ
  have haa : |1 / (1 + σ * κ)| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have h17 := ((reModel_iff_17_7 𝔼 (by linarith) i π).mp hπ).2
  have hf : Tendsto (fun t => σ * κ / (1 + σ * κ) * (i t ω - ib) +
      (π (t + 1) ω - 𝔼.E t (π (t + 1)) ω)) atTop (𝓝 0) := by
    simpa using ((hi.sub_const ib).const_mul (σ * κ / (1 + σ * κ))).add hδ
  have := tendsto_zero_of_stable haa (x := fun t => π t ω - ib) (fun t => by
    have e := h17 t ω
    linear_combination e + ib * hab) hf
  simpa using this.add_const ib

/-! ### The full model (17.18) under perfect foresight (§17.4.1, §17.4.3) -/

/-- Cochrane (2023), §17.4.3, p. 416 and eq. (5.6), p. 119: the open-mouth persistence is the
reciprocal of the larger root of `λ² − (1 + β + σκ)λ + β`, `η* = 1/λ₁`. -/
theorem etaStar_eq_inv_lam1 {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    etaStar σ κ β = (FullModel.lam1 σ β κ)⁻¹ := by
  have hs := Real.sq_sqrt (FullModel.disc_pos hσκ hβ0).le
  refine eq_inv_of_mul_eq_one_left ?_
  unfold etaStar FullModel.lam1
  set r := Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)
  field_simp
  linear_combination (-1 : ℝ) * hs

/-- Cochrane (2023), p. 408: the roots of `βλ² − (1 + β + σκ)λ + 1` are `η* = 1/λ₁` (stable)
and `1/λ₂` (unstable): `β η* λ₂⁻¹ = 1` and `β(η* + λ₂⁻¹) = 1 + β + σκ`. -/
theorem etaStar_mul_inv_lam2 {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    β * (etaStar σ κ β * (FullModel.lam2 σ β κ)⁻¹) = 1 ∧
      β * (etaStar σ κ β + (FullModel.lam2 σ β κ)⁻¹) = 1 + β + σ * κ := by
  have hp := FullModel.lam_prod hσκ hβ0
  have hs := FullModel.lam_sum σ β κ
  have h1 := (one_pos.trans (FullModel.one_lt_lam1 hσκ hβ0)).ne'
  have h2 := (FullModel.lam2_pos hσκ hβ0).ne'
  rw [etaStar_eq_inv_lam1 hσκ hβ0]
  set l1 := FullModel.lam1 σ β κ
  set l2 := FullModel.lam2 σ β κ
  constructor
  · calc β * (l1⁻¹ * l2⁻¹) = (l1 * l2) * (l1⁻¹ * l2⁻¹) := by rw [hp]
      _ = 1 := by field_simp
  · calc β * (l1⁻¹ + l2⁻¹) = (l1 * l2) * (l1⁻¹ + l2⁻¹) := by rw [hp]
      _ = l1 + l2 := by field_simp; ring
      _ = 1 + β + σ * κ := hs

/-- Cochrane (2023), p. 408: the unstable root `1/λ₂` exceeds one. -/
theorem one_lt_inv_lam2 {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    1 < (FullModel.lam2 σ β κ)⁻¹ :=
  (one_lt_inv₀ (FullModel.lam2_pos hσκ hβ0)).mpr (FullModel.lam2_lt_one hσκ hβ0)

/-- Cochrane (2023), §17.4.1, p. 410 and §17.4.3, p. 416, "there is no connection between the
persistence of the interest-rate shock and the sign of the inflation movement": in the full
model (17.18) under perfect foresight after the announcement (`FullModel.Second`), for every
bounded interest-rate path `i` (any persistence) and every announcement-date inflation `c` (any
sign) there is exactly one bounded equilibrium with `π_0 = c` — `FullModel.path σ β κ i c`
(`FullModel.pf_existsUnique`). -/
theorem full_any_sign {σ κ β M : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ n, |i n| ≤ M) (c : ℝ) :
    ∃! π : ℕ → ℝ, FullModel.Second σ β κ i π ∧ (∃ K, ∀ n, |π n| ≤ K) ∧ π 0 = c := by
  obtain ⟨π, ⟨hb, hs, h0⟩, hu⟩ := FullModel.pf_existsUnique hσκ hβ0 hi c
  exact ⟨π, ⟨hs, hb, h0⟩, fun π' ⟨hs', hb', h0'⟩ => hu π' ⟨hb', hs', h0'⟩⟩

/-- Cochrane (2023), §17.4.1, p. 408 (long-run response 1 in the full model): along the
equilibrium of `full_any_sign` (`FullModel.path`), if the rate converges, `i_n → ī`, inflation
converges to `ī`, whatever the announcement-date jump. -/
theorem full_long_run {σ κ β M ib : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ n, |i n| ≤ M) (hlim : Tendsto i atTop (𝓝 ib)) (c : ℝ) :
    Tendsto (FullModel.path σ β κ i c) atTop (𝓝 ib) :=
  FullModel.tendsto_pi hσκ hβ0 hi hlim (FullModel.path_bounded hσκ hβ0 hi c)
    ((FullModel.second_iff_factor hσκ hβ0 hi (FullModel.path_bounded hσκ hβ0 hi c)).mpr
      (FullModel.path_factor hσκ hβ0 i c))

end Cochrane.KeynesianStickyPrices.PersistenceFreedom
