/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5RandomRow

/-!
# Conditional expectations pass through absolutely convergent series

Cochrane (2023), §7.4, eq. (7.17), p. 225 (and every `E_t ∑` in the book).

`TidyR5RandomRow.theoremW_rowR` assumed `TidyR5RandomRow.SeriesExchange`: `E_t` passes through
absolutely convergent series of random variables. The question was whether a finitely additive
expectation system could violate it. It cannot: **`SeriesExchange` follows from the axioms of an
`ExpectationSystem`** (`seriesExchange`).

The reason is that `E_t` is linear and monotone on *all* random variables, unbounded ones
included. A finitely additive functional such as a Banach limit or a limit along a free
ultrafilter is defined only on bounded functions (or is infinite on some unbounded ones), so it is
not an `ExpectationSystem`. For a nonnegative series `F = ∑_n f_n` with tails `T_N`, the pointwise
bound (`tail_le_bound`)
`T_N ≤ ε + K h/(N+1) + F²/K`,
where `h` is the first index at which the tail falls below `ε`, together with linearity and
monotonicity, gives `E_t T_N → 0` (`E_tail_tendsto`). The two unbounded random variables `h` and
`F²` have finite expectations because `E_t` is defined on them.

Consequences: `theoremW_rowR'`, `price_formula_rowR'`, `formulaW_solves_rowR'` hold with no
interchange hypothesis, for every expectation system with the pull-out property.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange

open Filter Topology MaturityStructure GeneralFormula TidyR5RandomRow

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.4 (used for every `E_t ∑`): the tail `T_N = ∑_{n ≥ N} f_n` of a series of
random variables. -/
noncomputable def tailF (f : ℕ → Ω → ℝ) (N : ℕ) : Ω → ℝ := fun ω => ∑' n, f (n + N) ω

/-- Cochrane (2023), §7.4: tails of a nonnegative convergent series decrease, `T_{N'} ≤ T_N` for
`N ≤ N'`. -/
theorem tailF_anti {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) (ω : Ω) {N N' : ℕ} (h : N ≤ N') :
    tailF f N' ω ≤ tailF f N ω := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hs : Summable (fun n => f (n + N) ω) := (summable_nat_add_iff N).mpr (hfs ω)
  have := hs.sum_add_tsum_nat_add d
  simp only [tailF]
  rw [← this]
  have e : (fun n => f (n + d + N) ω) = fun n => f (n + (N + d)) ω := by
    funext n; congr 1; omega
  rw [← e]
  have : 0 ≤ ∑ i ∈ Finset.range d, f (i + N) ω := Finset.sum_nonneg fun i _ => hf0 _ ω
  linarith

/-- Cochrane (2023), §7.4: the tails of a series tend to zero at every state. -/
theorem tailF_tendsto (f : ℕ → Ω → ℝ) (ω : Ω) :
    Tendsto (fun N => tailF f N ω) atTop (𝓝 0) :=
  tendsto_sum_nat_add (fun n => f n ω)

/-- Cochrane (2023), §7.4: tails are nonnegative for a nonnegative series. -/
theorem tailF_nonneg {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω) (N : ℕ) (ω : Ω) :
    0 ≤ tailF f N ω :=
  tsum_nonneg fun _ => hf0 _ ω

/-- Cochrane (2023), §7.4: the first index at which the tail is at most `ε`. -/
noncomputable def firstIdx (f : ℕ → Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ :=
  (sInf {M : ℕ | tailF f M ω ≤ ε} : ℕ)

/-- Cochrane (2023), §7.4: **the pointwise tail bound** `T_N ≤ ε + K h/(N+1) + F²/K` for `ε, K > 0`,
with `h` the first index at which the tail falls below `ε` and `F = T_0`. -/
theorem tail_le_bound {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) (N : ℕ)
    (ω : Ω) :
    tailF f N ω ≤ ε + K * (firstIdx f ε ω / (N + 1)) + tailF f 0 ω ^ 2 / K := by
  have hT0 := tailF_nonneg hf0 N ω
  have hh0 : 0 ≤ firstIdx f ε ω := Nat.cast_nonneg _
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hF2 : 0 ≤ tailF f 0 ω ^ 2 / K := div_nonneg (sq_nonneg _) hK.le
  by_cases h : tailF f N ω ≤ ε
  · have : 0 ≤ K * (firstIdx f ε ω / (N + 1)) := mul_nonneg hK.le (div_nonneg hh0 hN1.le)
    linarith
  · push Not at h
    have hne : {M : ℕ | tailF f M ω ≤ ε}.Nonempty := by
      obtain ⟨M, hM⟩ := ((tailF_tendsto f ω).eventually (ge_mem_nhds hε)).exists
      exact ⟨M, hM⟩
    have hlt : N < sInf {M : ℕ | tailF f M ω ≤ ε} := by
      by_contra hc
      push Not at hc
      have h1 := tailF_anti hf0 hfs ω hc
      have h2 : tailF f (sInf {M : ℕ | tailF f M ω ≤ ε}) ω ≤ ε := Nat.sInf_mem hne
      linarith
    have hge : 1 ≤ firstIdx f ε ω / (N + 1) := by
      rw [le_div_iff₀ hN1, one_mul, firstIdx]
      exact_mod_cast hlt
    have hTF : tailF f N ω ≤ tailF f 0 ω := tailF_anti hf0 hfs ω (Nat.zero_le N)
    have hK1 : K ≤ K * (firstIdx f ε ω / (N + 1)) := by nlinarith
    by_cases hFK : tailF f 0 ω ≤ K
    · linarith
    · push Not at hFK
      have : tailF f 0 ω ≤ tailF f 0 ω ^ 2 / K := by
        rw [le_div_iff₀ hK]; nlinarith
      nlinarith

/-- Cochrane (2023), §7.4: **expectations of the tails tend to zero**, for every expectation
system: `E_t T_N → 0` for a nonnegative series converging at every state. -/
theorem E_tail_tendsto {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => 𝔼.E t (tailF f N) ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  set a : ℝ := 𝔼.E t (firstIdx f η) ω with ha
  set c : ℝ := 𝔼.E t (fun ω' => tailF f 0 ω' ^ 2) ω with hc
  have hnn : ∀ g : Ω → ℝ, (∀ ω', 0 ≤ g ω') → 0 ≤ 𝔼.E t g ω := fun g hg => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ g from hg) ω
    rwa [𝔼.const] at this
  have ha0 : 0 ≤ a := hnn _ fun ω' => Nat.cast_nonneg _
  have hc0 : 0 ≤ c := hnn _ fun ω' => sq_nonneg _
  set K : ℝ := c / η + 1 with hK
  have hK0 : 0 < K := by positivity
  have hcK : c / K ≤ η := by
    rw [div_le_iff₀ hK0, hK]
    have : c = c / η * η := by field_simp
    nlinarith
  refine ⟨⌈K * a / η⌉₊, fun N hN => ?_⟩
  have hN' : K * a / η ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hKa : K * (a / (N + 1)) ≤ η := by
    rw [div_le_iff₀ hη0] at hN'
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hb : tailF f N ≤ (fun _ => η) + (K / (N + 1)) • firstIdx f η +
      (1 / K) • fun ω' => tailF f 0 ω' ^ 2 := fun ω' => by
    have := tail_le_bound hf0 hfs hη0 hK0 N ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc tailF f N ω' ≤ η + K * (firstIdx f η ω' / (N + 1)) + tailF f 0 ω' ^ 2 / K := this
      _ = _ := by ring
  have hup := 𝔼.mono t hb ω
  rw [map_add, map_add, map_smul, map_smul, 𝔼.const] at hup
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hup
  have hlo := hnn _ (tailF_nonneg hf0 N)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlo]
  have e1 : K / (N + 1) * a = K * (a / (N + 1)) := by ring
  have e2 : 1 / K * c = c / K := by ring
  rw [← ha, ← hc, e1, e2] at hup
  linarith

/-- Cochrane (2023), §7.4: **`E_t` passes through nonnegative series**, for every expectation
system: `∑_n E_t f_n = E_t ∑_n f_n`. -/
theorem hasSum_E_nonneg {f : ℕ → Ω → ℝ} (hf0 : ∀ n ω, 0 ≤ f n ω)
    (hfs : ∀ ω, Summable (fun n => f n ω)) (t : ℕ) (ω : Ω) :
    HasSum (fun n => 𝔼.E t (f n) ω) (𝔼.E t (fun ω' => ∑' n, f n ω') ω) := by
  have hE0 : ∀ n, 0 ≤ 𝔼.E t (f n) ω := fun n => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ f n from fun ω' => hf0 n ω') ω
    rwa [𝔼.const] at this
  rw [hasSum_iff_tendsto_nat_of_nonneg hE0]
  have hpart : ∀ N, ∑ n ∈ Finset.range N, 𝔼.E t (f n) ω =
      𝔼.E t (fun ω' => ∑' n, f n ω') ω - 𝔼.E t (tailF f N) ω := by
    intro N
    have hfun : (fun ω' => ∑' n, f n ω') - tailF f N = ∑ n ∈ Finset.range N, f n := by
      funext ω'
      simp only [Pi.sub_apply, Finset.sum_apply, tailF]
      rw [← (hfs ω').sum_add_tsum_nat_add N]
      ring
    rw [← Pi.sub_apply, ← map_sub, hfun, map_sum, Finset.sum_apply]
  simp only [hpart]
  simpa using (tendsto_const_nhds (x := 𝔼.E t (fun ω' => ∑' n, f n ω') ω)).sub
    (E_tail_tendsto 𝔼 hf0 hfs t ω)

/-- Cochrane (2023), eq. (7.17), p. 225: **`SeriesExchange` is a theorem**: every expectation
system passes through absolutely convergent series of random variables. -/
theorem seriesExchange : SeriesExchange 𝔼 := by
  intro f hf t ω
  set fp : ℕ → Ω → ℝ := fun n ω' => max (f n ω') 0 with hfp
  set fm : ℕ → Ω → ℝ := fun n ω' => max (-f n ω') 0 with hfm
  have hp0 : ∀ n ω', 0 ≤ fp n ω' := fun n ω' => le_max_right _ _
  have hm0 : ∀ n ω', 0 ≤ fm n ω' := fun n ω' => le_max_right _ _
  have hps : ∀ ω', Summable (fun n => fp n ω') := fun ω' =>
    Summable.of_nonneg_of_le (fun n => hp0 n ω') (fun n => max_le (le_abs_self _)
      (abs_nonneg _)) (hf ω')
  have hms : ∀ ω', Summable (fun n => fm n ω') := fun ω' =>
    Summable.of_nonneg_of_le (fun n => hm0 n ω') (fun n => max_le (neg_le_abs _)
      (abs_nonneg _)) (hf ω')
  have hsplit : ∀ n, f n = fp n - fm n := fun n => by
    funext ω'
    simp only [hfp, hfm, Pi.sub_apply]
    rcases le_total 0 (f n ω') with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hsum : (fun ω' => ∑' n, f n ω') =
      (fun ω' => ∑' n, fp n ω') - fun ω' => ∑' n, fm n ω' := by
    funext ω'
    simp only [Pi.sub_apply]
    rw [← (hps ω').tsum_sub (hms ω')]
    exact tsum_congr fun n => congrFun (hsplit n) ω'
  have h := (hasSum_E_nonneg 𝔼 hp0 hps t ω).sub (hasSum_E_nonneg 𝔼 hm0 hms t ω)
  rw [hsum, map_sub, Pi.sub_apply]
  refine h.congr_fun fun n => ?_
  rw [hsplit n, map_sub, Pi.sub_apply]

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: (7.17) solves the flow system under the
row condition with random bounds, for every expectation system with the pull-out property. -/
theorem formulaW_solves_rowR' (hpo : 𝔼.PullOut) {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t, MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t) ∧
      (∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (formulaW 𝔼 β A s t ω)) ∧
      (∀ t ω, |formulaW 𝔼 β A s t ω| ≤ M / (1 - ρ)) ∧
      ∀ t, 𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t :=
  formulaW_solves_rowR 𝔼 hpo (seriesExchange 𝔼) hβ0 hρ1 h hA hs hsb

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W with random bounds, with no interchange
hypothesis**: under the row condition with random bounds (`ρ < 1`), each `A_t^{(t+j+1)}` known at
`t + j` and bounded adapted surpluses, every bounded solution of (7.14) is the weighted present
value (7.17), for every expectation system with the pull-out property. -/
theorem theoremW_rowR' (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (y t ω) :=
  theoremW_rowR 𝔼 hpo (seriesExchange 𝔼) hβ0 hρ1 h hA hs hsb hy hyb t ω

/-- Cochrane (2023), eq. (7.17), p. 225: (7.17) for the price level with random bounds, with no
interchange hypothesis. -/
theorem price_formula_rowR' (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (h : RowBoundR β (fracSold D) ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)))
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β (fracSold D) s t m ω) (D t t ω * x t ω) :=
  price_formula_rowR 𝔼 hpo (seriesExchange 𝔼) hβ0 hρ1 hD hDmm h hA hs hsb hflow hb t ω

end Cochrane.LongTermDebtDynamics.TidyR5SeriesExchange
