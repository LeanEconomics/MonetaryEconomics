/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.GlobalDynamics
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Monetary targeting, deflationary traps and inflationary panics

Woodford (2003), *Interest and Prices*, Chapter 2, §4.1 (eqs. (4.7)–(4.8), Figure 2.5),
§4.2 (eq. (4.9)) and §4.3 (eq. (4.10)), pp. 129–138. Perfect foresight throughout.

* **(4.7)–(4.8), p. 129.** `eq48_iff_fisher`: with `M_{t+1} = μ̄M_t`, the money-demand condition
  (3.3) (`i^m = 0`) and the Fisher equation (1.21) give `G(m_{t+1}) = (μ̄/β)F(m_t)`, where
  `F(m) = (U_c − U_m)m` and `G(m) = U_c m`.
* **Figure 2.5, p. 130 (separable case), error E7.** `F` is positive and strictly increasing
  with `F(0⁺) = 0` (`sepF_pos`, `sepF_strictMonoOn`, `sepF_tendsto_zero`), the successor map is
  `m ↦ (μ̄/β)(1 − v'(m)/c)m` (`eq48_sep_iff`), the steady state `m*` exists
  (`sep_exists_steady_state`) and the curve crosses the diagonal once, from below
  (`sep_single_crossing`). Convexity of `F`, asserted in the text, is false in general
  (`e7_counterexample`) and is not needed. Paths with `m₀ < m*` fall to zero
  (`sep_inflation_path`), paths with `m₀ > m*` grow without bound (`sep_deflation_path`).
* **(4.9), pp. 131–132.** With satiation and `μ̄ ≥ 1`, once real balances pass the satiation
  level the transversality condition fails (`money_tvc_violated`); hence every deflationary
  path of the separable model does (`sep_deflation_violates_tvc`).
* **pp. 132–133, error E4.** Under a Taylor rule and nominal government liabilities growing at
  `μ̄`, `β^Tλ(i_T)D_T/P_T` is multiplied by `μ̄/(1 + i_T)` each period (`tvcValue_succ`); so if
  eventually `1 + i_T ≤ μ̄` (not `≥`, as printed) the TVC (1.24) fails
  (`taylor_tvc_violated_of_eventually_le`). The printed inequality is false along every
  deflationary path (`e4_printed_inequality_false`), the corrected one holds
  (`e4_corrected_inequality`), giving `deflation_tvc_violated` (any limit `Π**` with
  `μ̄ > β⁻¹Π**`), `zero_bound_tvc_violated` (`φ = 0` below `Π̲ > β`, `μ̄ ≥ 1`) and
  `fig24_deflations_violate_tvc` (all self-fulfilling deflations of Figure 2.4, `μ̄ > 1`).
  The target path satisfies the TVC iff `βμ̄ < Π*` (`target_tvc_iff`).
* **p. 133.** With `β < μ̄ < 1` every path reaching satiation satisfies the TVC and (3.4), with
  inflation `β` thereafter, giving a continuum of equilibria (`money_contraction_continuum`).
* **(4.10), p. 136 (Obstfeld–Rogoff).** `sep_F_neg_of_or_condition`: (4.10) makes `F < 0` near
  zero; `or_no_path_below` (monotone-orbit argument) and the book's iterated bounds
  `or_bounds_exist` + `or_iteration_bound` + `or_paths_above_mstar` show that no
  perfect-foresight path ever has `m_t < m*`.
-/

namespace Woodford.PriceLevelDetermination.MoneyTargetingDynamics

open Filter Topology
open Woodford.PriceLevelDetermination.GlobalDynamics

/-! ## (4.7)–(4.8) -/

/-- Woodford (2003), (4.7), p. 129: `F(m) = [U_c(ȳ, m) − U_m(ȳ, m)]m`. -/
def Ffun (Uc Um : ℝ → ℝ) (m : ℝ) : ℝ := (Uc m - Um m) * m

/-- Woodford (2003), (4.7), p. 129: `G(m) = U_c(ȳ, m)m`. -/
def Gfun (Uc : ℝ → ℝ) (m : ℝ) : ℝ := Uc m * m

/-- Woodford (2003), (4.7)–(4.8), p. 129, derivation: at a date with `m_t = M_t/P_t`,
`m_{t+1} = μ̄M_t/P_{t+1}`, the money-demand condition (3.3) `U_m/U_c = i/(1+i)` (`i^m = 0`), and
`U_c > 0`, `U_c − U_m > 0`, the perfect-foresight Fisher equation (1.21) holds iff
`U_c(m_{t+1})m_{t+1} = (μ̄/β)[U_c(m_t) − U_m(m_t)]m_t`, i.e. `G(m_{t+1}) = (μ̄/β)F(m_t)`. -/
theorem eq48_iff_fisher {β μ P P1 M m m1 i uc uc1 um : ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hP : 0 < P) (hP1 : 0 < P1) (hM : 0 < M) (huc : 0 < uc) (huc1 : 0 < uc1)
    (hgap : 0 < uc - um) (hm : m = M / P) (hm1 : m1 = μ * M / P1)
    (h33 : um / uc = i / (1 + i)) (hi : 0 < 1 + i) :
    (1 + i = β⁻¹ * ((uc1 / uc) * (P / P1))⁻¹) ↔ uc1 * m1 = μ / β * ((uc - um) * m) := by
  have hi' : 1 + i = uc / (uc - um) := by
    rw [div_eq_div_iff huc.ne' hi.ne'] at h33
    rw [eq_div_iff hgap.ne']
    linarith
  have hR : β⁻¹ * ((uc1 / uc) * (P / P1))⁻¹ = uc * P1 / (β * uc1 * P) := by
    field_simp
  have eL : uc1 * (μ * M / P1) = (β * uc1 * P) * (μ * M / (β * P * P1)) := by
    field_simp
  have eR : μ / β * ((uc - um) * (M / P)) = ((uc - um) * P1) * (μ * M / (β * P * P1)) := by
    field_simp
  rw [hi', hR, div_eq_div_iff hgap.ne' (by positivity), hm, hm1, eL, eR,
    mul_left_inj' (ne_of_gt (by positivity))]
  constructor
  · intro h
    exact mul_left_cancel₀ huc.ne' (by linarith [h])
  · intro h
    rw [h]; ring

/-! ## The separable case: Figure 2.5 -/

/-- Woodford (2003), p. 130, additively separable case: `F(m) = (c − v'(m))m`, where `c > 0` is
the (constant) marginal utility of consumption at `ȳ` and `v'(m) = U_m`. -/
def sepF (c : ℝ) (vp : ℝ → ℝ) (m : ℝ) : ℝ := (c - vp m) * m

/-- Woodford (2003), Figure 2.5, p. 130: the graph `m ↦ G⁻¹((μ̄/β)F(m))` for `G(m) = cm`. -/
noncomputable def sepMap (β μ c : ℝ) (vp : ℝ → ℝ) (m : ℝ) : ℝ := μ / β * sepF c vp m / c

/-- Woodford (2003), (4.8), p. 130: in the separable case `G(m) = cm` is linear and can be
inverted, so `G(m') = (μ̄/β)F(m)` iff `m'` is the value of the map of Figure 2.5. -/
theorem eq48_sep_iff {β μ c m m' : ℝ} {vp : ℝ → ℝ} (hc : 0 < c) :
    c * m' = μ / β * sepF c vp m ↔ m' = sepMap β μ c vp m := by
  unfold sepMap
  rw [eq_div_iff hc.ne']
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 130: if `U_c − U_m = c − v'(m) > 0` for `m > 0`, then `F(m) > 0`. -/
theorem sepF_pos {c m : ℝ} {vp : ℝ → ℝ} (hgap : c - vp m > 0) (hm : 0 < m) : 0 < sepF c vp m :=
  mul_pos hgap hm

/-- Woodford (2003), p. 130, "`F(m)` equals `m` times an increasing function of `m`": with `v'`
nonincreasing (concave `v`) and `c − v' > 0`, `F` is strictly increasing on `(0, ∞)`. -/
theorem sepF_strictMonoOn {c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : StrictMonoOn (sepF c vp) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hvp : vp b ≤ vp a := hanti ha hb hab.le
  have h1 := hgap a ha'
  unfold sepF
  nlinarith

/-- Woodford (2003), p. 130, "takes the limiting value `F(0) = 0`": under the hypotheses of
`sepF_strictMonoOn`, `F(m) → 0` as `m → 0⁺`. -/
theorem sepF_tendsto_zero {c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : Tendsto (sepF c vp) (𝓝[>] 0) (𝓝 0) := by
  have hup : Tendsto (fun m : ℝ => (c - vp 1) * m) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun m : ℝ => (c - vp 1) * m) (𝓝 0) (𝓝 ((c - vp 1) * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with m hm
    exact (sepF_pos (by linarith [hgap m hm]) hm).le
  · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with m hm hm1
    unfold sepF
    have : vp 1 ≤ vp m := hanti hm (Set.mem_Ioi.mpr one_pos) hm1.2.le
    have hm' : (0 : ℝ) < m := hm
    nlinarith

/-- Woodford (2003), p. 130, "there is a second steady state, this time at zero real balances":
the map of Figure 2.5 tends to `0` as `m → 0⁺`. -/
theorem sepMap_tendsto_zero {β μ c : ℝ} {vp : ℝ → ℝ} (hanti : AntitoneOn vp (Set.Ioi 0))
    (hgap : ∀ m, 0 < m → vp m < c) : Tendsto (sepMap β μ c vp) (𝓝[>] 0) (𝓝 0) := by
  have := ((sepF_tendsto_zero hanti hgap).const_mul (μ / β)).div_const c
  rw [mul_zero, zero_div] at this
  exact this

/-- Woodford (2003), p. 130: the steady states of (4.8) are the `m > 0` with
`v'(m)/c = 1 − β/μ̄`, i.e. `U_m/U_c = Δ` at `1 + i = μ̄/β`, so `m* = L[ȳ, (μ̄ − β)/β]`. -/
theorem sepMap_fixed_iff {β μ c m : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hm : 0 < m) : sepMap β μ c vp m = m ↔ vp m = c * (1 - β / μ) := by
  unfold sepMap sepF
  rw [div_eq_iff hc.ne']
  constructor
  · intro h
    field_simp at h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), p. 130 and fn. 38: if `v'` is continuous on `(0, ∞)` and takes values on
both sides of `c(1 − β/μ̄)`, the steady state `m* > 0` exists. -/
theorem sep_exists_steady_state {β μ c a b : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hcont : ContinuousOn vp (Set.Ioi 0)) (ha : 0 < a) (hab : a ≤ b)
    (hva : c * (1 - β / μ) ≤ vp a) (hvb : vp b ≤ c * (1 - β / μ)) :
    ∃ ms, a ≤ ms ∧ ms ≤ b ∧ sepMap β μ c vp ms = ms := by
  obtain ⟨ms, hms, hv⟩ := intermediate_value_Icc' hab
    (hcont.mono fun z hz => (by linarith [hz.1] : (0 : ℝ) < z)) ⟨hvb, hva⟩
  exact ⟨ms, hms.1, hms.2, (sepMap_fixed_iff hβ hμ hc (by linarith [hms.1])).mpr hv⟩

/-- Woodford (2003), p. 130, "at this point the curve necessarily cuts the diagonal from below"
(single crossing, without any convexity): if `v'` is nonincreasing and `m*` is the only
`m > 0` with `v'(m) = v'(m*)` (e.g. `v'` strictly decreasing), then the map is below the
diagonal on `(0, m*)` and above it on `(m*, ∞)`. -/
theorem sep_single_crossing {β μ c ms : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hanti : AntitoneOn vp (Set.Ioi 0)) (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) :
    (∀ m, 0 < m → m < ms → sepMap β μ c vp m < m) ∧
      (∀ m, ms < m → m < sepMap β μ c vp m) := by
  have hv := (sepMap_fixed_iff hβ hμ hc hms).mp hfix
  have key : ∀ m, 0 < m →
      sepMap β μ c vp m - m = m * (c * (1 - β / μ) - vp m) * μ / (β * c) := by
    intro m _
    unfold sepMap sepF
    field_simp
    ring
  have hpos : ∀ m, 0 < m → 0 < m * μ / (β * c) := fun m hm => by positivity
  constructor
  · intro m hm hlt
    have h1 : vp ms ≤ vp m := hanti hm hms hlt.le
    have h2 : vp m ≠ vp ms := fun h => by linarith [huniq m hm h]
    have h3 : c * (1 - β / μ) - vp m < 0 := by
      rw [← hv]; exact sub_neg.mpr (lt_of_le_of_ne h1 h2.symm)
    have := key m hm
    have h4 : m * (c * (1 - β / μ) - vp m) * μ / (β * c) =
        (m * μ / (β * c)) * (c * (1 - β / μ) - vp m) := by ring
    rw [h4] at this
    nlinarith [hpos m hm]
  · intro m hlt
    have hm : 0 < m := by linarith
    have h1 : vp m ≤ vp ms := hanti hms hm hlt.le
    have h2 : vp m ≠ vp ms := fun h => by linarith [huniq m hm h]
    have h3 : 0 < c * (1 - β / μ) - vp m := by
      rw [← hv]; exact sub_pos.mpr (lt_of_le_of_ne h1 h2)
    have := key m hm
    have h4 : m * (c * (1 - β / μ) - vp m) * μ / (β * c) =
        (m * μ / (β * c)) * (c * (1 - β / μ) - vp m) := by ring
    rw [h4] at this
    nlinarith [hpos m hm]

/-- Woodford (2003), (4.8), p. 130: a perfect-foresight path of real balances in the separable
case: positive with `c m_{t+1} = (μ̄/β)F(m_t)` at all dates. -/
def IsSepPath (β μ c : ℝ) (vp : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, c * m (t + 1) = μ / β * sepF c vp (m t)

/-- Woodford (2003), p. 130, "a distinct perfect-foresight equilibrium corresponding to each
possible value of `m₀`": from every `m₀ > 0` the orbit of the map is a path, and a path is the
orbit of its initial value. -/
theorem sep_path_exists_unique {β μ c : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hgap : ∀ m, 0 < m → vp m < c) {m0 : ℝ} (hm0 : 0 < m0) :
    IsSepPath β μ c vp (fun t => (sepMap β μ c vp)^[t] m0) ∧
      ∀ m : ℕ → ℝ, IsSepPath β μ c vp m → m 0 = m0 → m = fun t => (sepMap β μ c vp)^[t] m0 := by
  have hsucc : ∀ t, (sepMap β μ c vp)^[t + 1] m0 = sepMap β μ c vp ((sepMap β μ c vp)^[t] m0) :=
    fun t => Function.iterate_succ_apply' _ _ _
  have hpos : ∀ t, 0 < (sepMap β μ c vp)^[t] m0 := by
    intro t
    induction t with
    | zero => exact hm0
    | succ n ih =>
      rw [hsucc]
      have := sepF_pos (c := c) (vp := vp) (by linarith [hgap _ ih]) ih
      unfold sepMap
      positivity
  refine ⟨⟨hpos, fun t => (eq48_sep_iff hc).mpr (hsucc t)⟩, fun m hm h0 => funext fun t => ?_⟩
  induction t with
  | zero => exact h0
  | succ n ih => rw [(eq48_sep_iff hc).mp (hm.2 n), ih, hsucc]

/-- Woodford (2003), p. 130, "if `m₀ < m*`, real balances must be expected to decrease over
time …, converging to zero asymptotically. This corresponds to a self-fulfilling inflation":
strictly decreasing, tending to `0`. -/
theorem sep_inflation_path {β μ c ms : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0)) (hcont : ContinuousOn vp (Set.Ioi 0))
    (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hpath : IsSepPath β μ c vp m)
    (h0 : m 0 < ms) : StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  have hsc := (sep_single_crossing hβ hμ hc hanti hms hfix huniq).1
  have hrec : ∀ t, m (t + 1) = sepMap β μ c vp (m t) := fun t => (eq48_sep_iff hc).mp (hpath.2 t)
  have hstep : ∀ t, m t < ms ∧ m (t + 1) < m t := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hrec]; exact hsc _ (hpath.1 0) h0⟩
    | succ n ih =>
      have h1 : m (n + 1) < ms := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hrec (n + 1)]; exact hsc _ (hpath.1 _) h1⟩
  have hsa : StrictAnti m := strictAnti_nat_of_succ_lt fun t => (hstep t).2
  refine ⟨hsa, ?_⟩
  rcases antitone_orbit_atBot_or_fixed hrec hsa.antitone with h | ⟨L, hL, hbd, hfixL⟩
  · exfalso
    obtain ⟨t, ht⟩ := (h.eventually (eventually_le_atBot (0 : ℝ))).exists
    linarith [hpath.1 t]
  · have hL0 : 0 ≤ L := ge_of_tendsto hL (Eventually.of_forall fun t => (hpath.1 t).le)
    rcases hL0.lt_or_eq with hLpos | hL0
    · exfalso
      have hcL : ContinuousAt (sepMap β μ c vp) L := by
        have : ContinuousAt vp L := hcont.continuousAt (Ioi_mem_nhds hLpos)
        unfold sepMap sepF
        exact ((continuousAt_const.mul ((continuousAt_const.sub this).mul continuousAt_id))).div
          continuousAt_const hc.ne'
      have hf := hfixL hcL
      have hLms : L < ms := lt_of_le_of_lt (hbd 0) h0
      have := hsc L hLpos hLms
      linarith
    · rw [← hL0] at hL; exact hL

/-- Woodford (2003), p. 131, "if instead `m₀ > m*`, real balances must increase over time,
eventually increasing without bound" (the self-fulfilling deflation of monetary targeting). -/
theorem sep_deflation_path {β μ c ms : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0)) (hcont : ContinuousOn vp (Set.Ioi 0))
    (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hpath : IsSepPath β μ c vp m)
    (h0 : ms < m 0) : StrictMono m ∧ Tendsto m atTop atTop := by
  have hsc := (sep_single_crossing hβ hμ hc hanti hms hfix huniq).2
  have hrec : ∀ t, m (t + 1) = sepMap β μ c vp (m t) := fun t => (eq48_sep_iff hc).mp (hpath.2 t)
  have hstep : ∀ t, ms < m t ∧ m t < m (t + 1) := by
    intro t
    induction t with
    | zero => exact ⟨h0, by rw [hrec]; exact hsc _ h0⟩
    | succ n ih =>
      have h1 : ms < m (n + 1) := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hrec (n + 1)]; exact hsc _ h1⟩
  have hsm : StrictMono m := strictMono_nat_of_lt_succ fun t => (hstep t).2
  refine ⟨hsm, ?_⟩
  rcases monotone_orbit_atTop_or_fixed hrec hsm.monotone with h | ⟨L, _, hbd, hfixL⟩
  · exact h
  · exfalso
    have hLpos : 0 < L := by linarith [hbd 0]
    have hcL : ContinuousAt (sepMap β μ c vp) L := by
      have : ContinuousAt vp L := hcont.continuousAt (Ioi_mem_nhds hLpos)
      unfold sepMap sepF
      exact ((continuousAt_const.mul ((continuousAt_const.sub this).mul continuousAt_id))).div
        continuousAt_const hc.ne'
    have hf := hfixL hcL
    have := hsc L (by linarith [hbd 0])
    linarith

/-- Woodford (2003), p. 130, error E7: the counterexample `F(m) = m(1 − e^{−m})`
(`u = log c + v(m)`, `ȳ = 1`, `v'(m) = e^{−m}`). -/
noncomputable def vpE7 (m : ℝ) : ℝ := Real.exp (-m)

/-- Woodford (2003), p. 130, error E7: "`F(m)` is positive, increasing, and convex" — convexity
is false. For `c = 1`, `v'(m) = e^{−m}` all the hypotheses of Figure 2.5 hold (`v'` continuous,
strictly decreasing, `0 < v' < c`), so `F` is positive, strictly increasing and tends to `0` at
`0⁺`, yet `F` is not convex on `(0, ∞)`: `F(3) > (F(2) + F(4))/2`. -/
theorem e7_counterexample :
    ContinuousOn vpE7 (Set.Ioi 0) ∧ StrictAntiOn vpE7 (Set.Ioi 0) ∧
      (∀ m, 0 < m → 0 < vpE7 m ∧ vpE7 m < 1) ∧
      (∀ m, 0 < m → 0 < sepF 1 vpE7 m) ∧ StrictMonoOn (sepF 1 vpE7) (Set.Ioi 0) ∧
      Tendsto (sepF 1 vpE7) (𝓝[>] 0) (𝓝 0) ∧
      (sepF 1 vpE7 2 + sepF 1 vpE7 4) / 2 < sepF 1 vpE7 3 ∧
      ¬ ConvexOn ℝ (Set.Ioi 0) (sepF 1 vpE7) := by
  have hsa : StrictAntiOn vpE7 (Set.Ioi 0) := fun a _ b _ hab => by
    unfold vpE7; exact Real.exp_lt_exp.mpr (by linarith)
  have hbd : ∀ m, 0 < m → 0 < vpE7 m ∧ vpE7 m < 1 := fun m hm => by
    unfold vpE7
    exact ⟨Real.exp_pos _, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)⟩
  have hgap : ∀ m, 0 < m → vpE7 m < 1 := fun m hm => (hbd m hm).2
  have hmid : (sepF 1 vpE7 2 + sepF 1 vpE7 4) / 2 < sepF 1 vpE7 3 := by
    unfold sepF vpE7
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0); linarith
    have e2 : Real.exp (-2) = Real.exp (-4) * Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have e3 : Real.exp (-3) = Real.exp (-4) * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [e2, e3]
    have h4 := Real.exp_pos (-4)
    nlinarith [mul_pos h4 (mul_pos (by linarith : (0 : ℝ) < Real.exp 1 - 1)
      (by linarith : (0 : ℝ) < Real.exp 1 - 2))]
  refine ⟨fun m _ => (Real.continuous_exp.comp continuous_neg).continuousAt.continuousWithinAt,
    hsa, hbd, fun m hm => sepF_pos (by linarith [hgap m hm]) hm,
    sepF_strictMonoOn hsa.antitoneOn hgap, sepF_tendsto_zero hsa.antitoneOn hgap, hmid, ?_⟩
  intro hconv
  have := hconv.2 (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 4)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  norm_num at this
  linarith

/-! ## (4.9): satiation and the transversality condition under monetary targeting -/

/-- Woodford (2003), (4.8), p. 129, general (possibly nonseparable) utility: a perfect-foresight
path of real balances, positive with `G(m_{t+1}) = (μ̄/β)F(m_t)`. -/
def IsPath48 (β μ : ℝ) (Uc Um : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, Gfun Uc (m (t + 1)) = μ / β * Ffun Uc Um (m t)

/-- Woodford (2003), pp. 131–132: satiation at `m̄`: for `m ≥ m̄`, `U_m = 0` and `U_c` is constant
(`F = G` there). -/
def Satiation (Uc Um : ℝ → ℝ) (msat : ℝ) : Prop := ∀ m, msat ≤ m → Um m = 0 ∧ Uc m = Uc msat

/-- Woodford (2003), p. 131, "(4.8) requires that `m_{t+1} = μ̄/β m_t` each period, after real
balances exceed the satiation level": with `G` strictly increasing, `μ̄ ≥ β` and satiation at
`m̄`, a path that reaches `m̄` at `t₀` satisfies `m_{t₀+n} = (μ̄/β)ⁿ m_{t₀} ≥ m̄` for all `n`. -/
theorem satiated_path {β μ msat : ℝ} {Uc Um : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμβ : β ≤ μ)
    (hsat : Satiation Uc Um msat) (hUc : 0 < Uc msat) (hmsat : 0 < msat)
    (hG : StrictMonoOn (Gfun Uc) (Set.Ioi 0)) (hpath : IsPath48 β μ Uc Um m) {t0 : ℕ}
    (ht0 : msat ≤ m t0) : ∀ n, msat ≤ m (t0 + n) ∧ m (t0 + n) = (μ / β) ^ n * m t0 := by
  intro n
  induction n with
  | zero => simp [ht0]
  | succ n ih =>
    have hs := hsat _ ih.1
    have heq := hpath.2 (t0 + n)
    unfold Gfun Ffun at heq
    rw [hs.1, hs.2, sub_zero] at heq
    have hratio : 1 ≤ μ / β := (one_le_div hβ).mpr hμβ
    have hge : msat ≤ m (t0 + n + 1) := by
      by_contra hcon
      push Not at hcon
      have h1 : Gfun Uc (m (t0 + n + 1)) < Gfun Uc msat :=
        hG (hpath.1 _) (Set.mem_Ioi.mpr hmsat) hcon
      unfold Gfun at h1
      rw [heq] at h1
      have h2 : Uc msat * msat ≤ Uc msat * m (t0 + n) := mul_le_mul_of_nonneg_left ih.1 hUc.le
      have h3 : Uc msat * m (t0 + n) ≤ μ / β * (Uc msat * m (t0 + n)) :=
        le_mul_of_one_le_left (by nlinarith [hpath.1 (t0 + n)]) hratio
      linarith
    have hs1 := hsat _ hge
    rw [hs1.2] at heq
    have hm1 : m (t0 + n + 1) = μ / β * m (t0 + n) :=
      mul_left_cancel₀ hUc.ne' (by rw [heq]; ring)
    refine ⟨by rw [← add_assoc]; exact hge, ?_⟩
    rw [← add_assoc, hm1, ih.2, pow_succ]
    ring

/-- Woodford (2003), (4.9), p. 132, "the transversality condition is violated in the case of
any such path": with `0 < β`, `μ̄ ≥ 1`, satiation at `m̄ > 0`, `G` strictly increasing and a path
reaching `m̄`, `β^T U_c(m_T)m_T = β^{t₀}μ̄^{T−t₀}U_c m_{t₀} ≥ β^{t₀}U_c m_{t₀} > 0` for `T ≥ t₀`, so
`β^T U_c(m_T) m_T` does not tend to `0`. -/
theorem money_tvc_violated {β μ msat : ℝ} {Uc Um : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hμ : 1 ≤ μ) (hsat : Satiation Uc Um msat) (hUc : 0 < Uc msat)
    (hmsat : 0 < msat) (hG : StrictMonoOn (Gfun Uc) (Set.Ioi 0)) (hpath : IsPath48 β μ Uc Um m)
    {t0 : ℕ} (ht0 : msat ≤ m t0) :
    (∀ n, β ^ (t0 + n) * Uc (m (t0 + n)) * m (t0 + n) =
        β ^ t0 * μ ^ n * Uc (m t0) * m t0) ∧
      ¬ Tendsto (fun T => β ^ T * Uc (m T) * m T) atTop (𝓝 0) := by
  have hsp := satiated_path hβ (by linarith) hsat hUc hmsat hG hpath ht0
  have hval : ∀ n, β ^ (t0 + n) * Uc (m (t0 + n)) * m (t0 + n) =
      β ^ t0 * μ ^ n * Uc (m t0) * m t0 := by
    intro n
    rw [(hsat _ (hsp n).1).2, (hsat _ ht0).2, (hsp n).2, pow_add, div_pow]
    field_simp
  refine ⟨hval, fun h => ?_⟩
  have hpos : 0 < β ^ t0 * Uc (m t0) * m t0 := by
    rw [(hsat _ ht0).2]; have := hpath.1 t0; positivity
  have hev : ∀ᶠ T in atTop, β ^ t0 * Uc (m t0) * m t0 ≤ β ^ T * Uc (m T) * m T := by
    filter_upwards [eventually_ge_atTop t0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    rw [hval n]
    have h1 : 1 ≤ μ ^ n := one_le_pow₀ hμ
    have : β ^ t0 * Uc (m t0) * m t0 * 1 ≤ β ^ t0 * Uc (m t0) * m t0 * μ ^ n :=
      mul_le_mul_of_nonneg_left h1 hpos.le
    linarith
  have := ge_of_tendsto h hev
  linarith

/-- Woodford (2003), pp. 131–132, combined: in the separable model with satiation at `m̄`
(`v' = 0` on `[m̄, ∞)`) and `μ̄ ≥ 1`, every deflationary path (`m₀ > m*`) violates the
transversality condition (4.9), so it is not an equilibrium. -/
theorem sep_deflation_violates_tvc {β μ c ms msat : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (hμ : 1 ≤ μ) (hc : 0 < c) (hanti : AntitoneOn vp (Set.Ioi 0))
    (hcont : ContinuousOn vp (Set.Ioi 0)) (hms : 0 < ms) (hfix : sepMap β μ c vp ms = ms)
    (huniq : ∀ m, 0 < m → vp m = vp ms → m = ms) (hmsat : 0 < msat)
    (hsat : ∀ m, msat ≤ m → vp m = 0) (hpath : IsSepPath β μ c vp m) (h0 : ms < m 0) :
    ¬ Tendsto (fun T => β ^ T * (fun _ : ℝ => c) (m T) * m T) atTop (𝓝 0) := by
  have hdef := sep_deflation_path hβ (by linarith) hc hanti hcont hms hfix huniq hpath h0
  obtain ⟨t0, ht0⟩ := (hdef.2.eventually (eventually_ge_atTop msat)).exists
  refine (money_tvc_violated (Uc := fun _ => c) (Um := vp) hβ hβ1 hμ
    (fun m hm => ⟨hsat m hm, rfl⟩) hc hmsat
    (fun a _ b _ hab => by unfold Gfun; nlinarith) ⟨hpath.1, fun t => ?_⟩ ht0).2
  have := hpath.2 t
  unfold Gfun Ffun
  unfold sepF at this
  linarith

/-- Woodford (2003), p. 133, "under the monetary targeting regime … the previous argument …
fails when `μ̄ < 1`. In this case, the transversality condition is satisfied by all of the
solutions to (4.8) that involve inflation rates eventually falling to the level `Π_t = β`, and
so a continuum of perfect-foresight equilibria … exists": with satiation at `m̄ > 0`, `U_c` constant
above `m̄` and `β < μ̄ < 1`, each `m₀ ≥ m̄` starts the path `m_t = (μ̄/β)^t m₀` of (4.8), distinct
for distinct `m₀`; along it inflation `μ̄m_t/m_{t+1}` equals `β`, the transversality condition
holds and the bound (3.4) converges. -/
theorem money_contraction_continuum {β μ msat ybar : ℝ} {Uc Um : ℝ → ℝ} (hβ : 0 < β)
    (hβμ : β < μ) (hμ1 : μ < 1) (hsat : Satiation Uc Um msat) {m0 : ℝ} (hm0 : msat ≤ m0)
    (hmsat : 0 < msat) :
    IsPath48 β μ Uc Um (fun t => (μ / β) ^ t * m0) ∧
      (∀ t, μ * ((μ / β) ^ t * m0) / ((μ / β) ^ (t + 1) * m0) = β) ∧
      Tendsto (fun T => β ^ T * Uc ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0)) atTop (𝓝 0) ∧
      Summable (fun T => β ^ T * (Uc ((μ / β) ^ T * m0) * ybar +
        Um ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0))) := by
  have hm0pos : 0 < m0 := by linarith
  have hr : 1 ≤ μ / β := (one_le_div hβ).mpr hβμ.le
  have hge : ∀ t, msat ≤ (μ / β) ^ t * m0 := fun t =>
    le_trans hm0 (le_mul_of_one_le_left hm0pos.le (one_le_pow₀ hr))
  have hμ0 : 0 < μ := by linarith
  refine ⟨⟨fun t => by positivity, fun t => ?_⟩, fun t => ?_, ?_, ?_⟩
  · unfold Gfun Ffun
    rw [(hsat _ (hge t)).1, (hsat _ (hge (t + 1))).2, (hsat _ (hge t)).2]
    simp only [pow_succ]
    ring
  · rw [pow_succ]
    field_simp
  · have hcongr : (fun T => β ^ T * Uc ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0)) =
        fun T => μ ^ T * (Uc msat * m0) := by
      funext T
      rw [(hsat _ (hge T)).2, div_pow]
      field_simp
    rw [hcongr]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0.le hμ1).mul_const (Uc msat * m0)
  · have hcongr : (fun T => β ^ T * (Uc ((μ / β) ^ T * m0) * ybar +
        Um ((μ / β) ^ T * m0) * ((μ / β) ^ T * m0))) = fun T => β ^ T * (Uc msat * ybar) := by
      funext T
      rw [(hsat _ (hge T)).1, (hsat _ (hge T)).2]
      ring
    rw [hcongr]
    exact (summable_geometric_of_lt_one hβ.le (by linarith)).mul_right _

/-! ## The Taylor-rule version: nominal liabilities growing at `μ̄` (pp. 132–133) -/

/-- Woodford (2003), (1.24), p. 72, along a perfect-foresight path: the transversality term
`β^T λ(i_T) D_T/P_T` with `i_T = φ(Π_T)`. -/
noncomputable def tvcValue (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ P D : ℕ → ℝ) (T : ℕ) : ℝ :=
  β ^ T * lam (φ (Pi_ T)) * D T / P T

/-- Woodford (2003), p. 133, displayed identity: when `P_{t+1} = Π_{t+1}P_t`,
`D_{t+1} = μ̄D_t` and (4.5) holds,
`β^{T+1}λ_{T+1}D_{T+1}/P_{T+1} = β^Tλ_TD_T/P_T · μ̄/(1 + i_T)`. -/
theorem tvcValue_succ {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t) (T : ℕ) :
    tvcValue β lam φ Pi_ P D (T + 1) = tvcValue β lam φ Pi_ P D T * (μ / (1 + φ (Pi_ T))) := by
  have h45 := hpath.2 T
  have hl1 := hlam (T + 1)
  have hl := hlam T
  have hPi := hpath.1 (T + 1)
  have hφT := hφ T
  have hPT := hP T
  have hlam1 : lam (φ (Pi_ (T + 1))) = Pi_ (T + 1) * lam (φ (Pi_ T)) / (β * (1 + φ (Pi_ T))) := by
    rw [div_eq_div_iff hl1.ne' hl.ne'] at h45
    rw [eq_div_iff (by positivity)]
    linarith
  unfold tvcValue
  rw [hlam1, hPrec, hD, pow_succ]
  field_simp

/-- Woodford (2003), pp. 132–133 (error E4 corrected): if from some date on `1 + i_T ≤ μ̄`, the
transversality term is nondecreasing and positive from that date, so the transversality
condition (1.24) is violated. -/
theorem taylor_tvc_violated_of_eventually_le {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hev : ∃ t0, ∀ T, t0 ≤ T → 1 + φ (Pi_ T) ≤ μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t0, ht0⟩ := hev
  have hpos : ∀ T, 0 < tvcValue β lam φ Pi_ P D T := fun T => by
    unfold tvcValue; have := hlam T; have := hDpos T; have := hP T; positivity
  have hmono : ∀ n, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D (t0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, tvcValue_succ hβ hpath hlam hφ hP hPrec hD]
      have h1 : 1 ≤ μ / (1 + φ (Pi_ (t0 + n))) :=
        (one_le_div (hφ _)).mpr (ht0 _ (Nat.le_add_right _ _))
      nlinarith [hpos (t0 + n)]
  intro h
  have hev : ∀ᶠ T in atTop, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D T := by
    filter_upwards [eventually_ge_atTop t0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hmono n
  have := ge_of_tendsto h hev
  linarith [hpos t0]

/-- Woodford (2003), p. 133, error E4: the printed claim "there must exist a date `t` such that
`1 + φ(Π_T) ≥ μ̄` for all `T ≥ t`" is false along any deflationary path converging to a point
`Π**` where `φ` is continuous with `1 + φ(Π**) < μ̄` (in Figure 2.4, `Π** = β`, `φ(β) = 0`,
`μ̄ > 1`). -/
theorem e4_printed_inequality_false {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ¬ ∃ t, ∀ T, t ≤ T → μ ≤ 1 + φ (Pi_ T) := by
  rintro ⟨t, ht⟩
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  have h2 : ∀ᶠ T in atTop, μ ≤ 1 + φ (Pi_ T) := by
    filter_upwards [eventually_ge_atTop t] with T hT using ht T hT
  have := ge_of_tendsto h1 h2
  linarith

/-- Woodford (2003), p. 133, error E4 corrected: under the same hypotheses there is a date after
which `1 + φ(Π_T) ≤ μ̄` (indeed `<`). -/
theorem e4_corrected_inequality {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ∃ t, ∀ T, t ≤ T → 1 + φ (Pi_ T) ≤ μ := by
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  obtain ⟨t, ht⟩ := eventually_atTop.mp (h1.eventually (gt_mem_nhds hμ))
  exact ⟨t, fun T hT => (ht T hT).le⟩

/-- Woodford (2003), p. 133, "even if interest rates level off sooner, so that there exists a
lower steady-state inflation rate `Π** > β`, the same argument works as long as `μ̄ > β⁻¹Π**`":
a path of (4.5) converging to a steady state `Π**` (so `1 + φ(Π**) = β⁻¹Π**`) with `φ` continuous
there and `μ̄ > β⁻¹Π**` violates the transversality condition. -/
theorem deflation_tvc_violated {β μ Pss : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ0 : ∀ t, 0 ≤ φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss)
    (hss : 1 + φ Pss = Pss / β) (hμ : Pss / β < μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) :=
  taylor_tvc_violated_of_eventually_le hβ hpath hlam (fun t => by linarith [hφ0 t]) hP hPrec hD
    hDpos (e4_corrected_inequality hlim hcont (by rw [hss]; exact hμ))

/-- Woodford (2003), p. 132: if `φ(Π) = 0` for all `Π ≤ Π̲` with `Π̲ > β`, a path of (4.5) that is
eventually below `Π̲` has `i_T = 0` and then `Π_{T+1} = β` from that date on. -/
theorem zero_bound_inflation_eq_beta {β Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hpath : IsPath45 β lam φ Pi_) (hlam0 : 0 < lam 0) (hzero : ∀ x, x ≤ Plow → φ x = 0)
    {t : ℕ} (ht : ∀ T, t ≤ T → Pi_ T ≤ Plow) : ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β := by
  intro T hT
  have h1 := hzero _ (ht T hT)
  have h2 := hzero _ (ht (T + 1) (by omega))
  have h45 := hpath.2 T
  rw [h1, h2, add_zero, mul_one] at h45
  exact ⟨h1, by rwa [div_left_inj' hlam0.ne'] at h45⟩

/-- Woodford (2003), p. 132, "then any deflationary solution to (4.5) involves a zero nominal
interest rate in each period after some finite date `t`, which in turn implies that `Π_T = β`
for all `T ≥ t + 1`. It follows that … the transversality condition (1.24) is violated": with
`φ = 0` on `(−∞, Π̲]`, `Π̲ > β`, `D` growing at `μ̄ ≥ 1`, a path of (4.5) converging to `β`
eventually has `i = 0` and `Π = β`, and violates (1.24). -/
theorem zero_bound_tvc_violated {β μ Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hPlow : β < Plow) (hμ : 1 ≤ μ) (hpath : IsPath45 β lam φ Pi_)
    (hlam : ∀ t, 0 < lam (φ (Pi_ t))) (hlam0 : 0 < lam 0) (hφ0 : ∀ t, 0 ≤ φ (Pi_ t))
    (hzero : ∀ x, x ≤ Plow → φ x = 0) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 β)) :
    (∃ t, ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β) ∧
      ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t, ht⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hPlow))
  have hz := zero_bound_inflation_eq_beta hpath hlam0 hzero (fun T hT => (ht T hT).le)
  refine ⟨⟨t, hz⟩, taylor_tvc_violated_of_eventually_le hβ hpath hlam
    (fun s => by linarith [hφ0 s]) hP hPrec hD hDpos ⟨t, fun T hT => ?_⟩⟩
  rw [(hz T hT).1]; linarith

/-- Woodford (2003), p. 133, "even if `φ(Π) > 0` for all `Π > β`, as long as
`φ(Π) < (Π − β)/β` for all `β < Π < Π*`, one can still exclude self-fulfilling deflations in the
case of any fiscal policy that ensures a growth rate `μ̄ > 1` for government liabilities": under
the hypotheses of Figure 2.4 (`GlobalDynamics.self_fulfilling_deflation45`), every solution of
(4.5) starting in `(β, Π*)` violates the transversality condition (1.24). -/
theorem fig24_deflations_violate_tvc {β Pis μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hμ : 1 < μ) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) : ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  have hlim := (self_fulfilling_deflation45 hβ hlam hanti hlamc hmono hφ0 hcont hφβ hbelow
    hpath h0).2.2
  exact deflation_tvc_violated hβ hpath (fun t => hlam _ (hφ0 _ (hpath.1 t)))
    (fun t => hφ0 _ (hpath.1 t)) hP hPrec hD hDpos hlim
    (hcont.continuousAt (Ioi_mem_nhds hβ)) (by rw [hφβ, div_self hβ.ne']; ring)
    (by rw [div_self hβ.ne']; exact hμ)

/-- Woodford (2003), pp. 132–133 (implicit): along the target path `Π_t ≡ Π*` (with
`1 + φ(Π*) = Π*/β`) the transversality term is `(βμ̄/Π*)^T` times its initial value, so the target
equilibrium satisfies (1.24) iff `βμ̄ < Π*` (given `μ̄ > 0`). -/
theorem target_tvc_iff {β μ Pis : ℝ} {lam φ : ℝ → ℝ} {P D : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hPis : 0 < Pis) (htarget : 1 + φ Pis = Pis / β) (hlam : 0 < lam (φ Pis))
    (hP : ∀ t, 0 < P t) (hPrec : ∀ t, P (t + 1) = Pis * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    Tendsto (tvcValue β lam φ (fun _ => Pis) P D) atTop (𝓝 0) ↔ β * μ < Pis := by
  have hpath : IsPath45 β lam φ (fun _ => Pis) := ⟨fun _ => hPis, fun _ => by
    simp only [htarget]; field_simp⟩
  have hval : ∀ T, tvcValue β lam φ (fun _ => Pis) P D T =
      tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [tvcValue_succ hβ hpath (fun _ => hlam) (fun _ => by rw [htarget]; positivity) hP hPrec
        hD, ih, htarget, pow_succ]
      field_simp
  have h0 : 0 < tvcValue β lam φ (fun _ => Pis) P D 0 := by
    unfold tvcValue; have := hDpos 0; have := hP 0; positivity
  have hr0 : 0 ≤ β * μ / Pis := by positivity
  rw [show tvcValue β lam φ (fun _ => Pis) P D =
    fun T => tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T from funext hval]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hr1 : 1 ≤ β * μ / Pis := (one_le_div hPis).mpr hcon
    have hev : ∀ᶠ T in atTop, tvcValue β lam φ (fun _ => Pis) P D 0 ≤
        tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T :=
      Eventually.of_forall fun T => le_mul_of_one_le_right h0.le (one_le_pow₀ hr1)
    have := ge_of_tendsto h hev
    linarith
  · intro h
    have hr1 : β * μ / Pis < 1 := (div_lt_one hPis).mpr h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (tvcValue β lam φ (fun _ => Pis) P D 0)

/-! ## (4.10): Obstfeld and Rogoff -/

/-- Woodford (2003), (4.10), p. 136: in the separable case, `lim_{m→0⁺} m u_m(m) = ℓ > 0` implies
that `F(m) = (c − v'(m))m` is negative on some interval `(0, m̲]`. -/
theorem sep_F_neg_of_or_condition {c ℓ : ℝ} {vp : ℝ → ℝ} (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun m => m * vp m) (𝓝[>] 0) (𝓝 ℓ)) :
    ∃ mlow, 0 < mlow ∧ ∀ m, 0 < m → m ≤ mlow → sepF c vp m < 0 := by
  have hF : Tendsto (sepF c vp) (𝓝[>] 0) (𝓝 (c * 0 - ℓ)) := by
    have h1 : Tendsto (fun m : ℝ => c * m) (𝓝[>] 0) (𝓝 (c * 0)) :=
      ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    have : sepF c vp = fun m => c * m - m * vp m := by funext m; unfold sepF; ring
    rw [this]
    exact h1.sub hlim
  have hev : ∀ᶠ m in 𝓝[>] 0, sepF c vp m < 0 := hF.eventually (gt_mem_nhds (by linarith))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨u / 2, by linarith [Set.mem_Ioi.mp hu], fun m hm hmu => hsub ⟨hm, by
    linarith [Set.mem_Ioi.mp hu]⟩⟩

/-- Woodford (2003), (4.8) with `G(m) = cm`: a perfect-foresight path for a general `F`. -/
def IsORPath (β μ c : ℝ) (F : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, c * m (t + 1) = μ / β * F (m t)

/-- Woodford (2003), p. 136, "thus no equilibrium can ever have `m_t ≤ m̲`": if `F ≤ 0` on
`(0, m̲]`, every path has `m_t > m̲`. -/
theorem or_path_above_mlow {β μ c mlow : ℝ} {F : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0) (hpath : IsORPath β μ c F m) (t : ℕ) :
    mlow < m t := by
  by_contra hcon
  push Not at hcon
  have h1 := hFneg _ (hpath.1 t) hcon
  have h2 := hpath.2 t
  have h3 : 0 < c * m (t + 1) := mul_pos hc (hpath.1 _)
  have h4 : μ / β * F (m t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
  linarith

/-- Woodford (2003), (4.10), p. 136, "one shows in this way that no equilibrium is possible
with `m_t < m*` at any time" (proof by the monotone-orbit lemma L5): if `F ≤ 0` on `(0, m̲]`,
`F` is continuous on `(0, ∞)`, `m*` is a steady state and the curve is below the diagonal on
`[m̲, m*)`, every perfect-foresight path has `m_t ≥ m*` at all dates. -/
theorem or_no_path_below {β μ c mlow ms : ℝ} {F : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hmlow : 0 < mlow) (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0)
    (hFc : ContinuousOn F (Set.Ioi 0))
    (hbelow : ∀ x, mlow ≤ x → x < ms → F x < β / μ * (c * x)) (hpath : IsORPath β μ c F m) :
    ∀ t, ms ≤ m t := by
  intro t0
  by_contra hcon
  push Not at hcon
  set g : ℝ → ℝ := fun x => μ / β * F x / c with hg
  have hrec : ∀ t, m (t + 1) = g (m t) := fun t => by
    rw [hg, eq_div_iff hc.ne', mul_comm]; exact hpath.2 t
  have hdown : ∀ x, mlow ≤ x → x < ms → g x < x := by
    intro x h1 h2
    have := hbelow x h1 h2
    rw [hg, div_lt_iff₀ hc]
    have h3 : μ / β * F x < μ / β * (β / μ * (c * x)) := mul_lt_mul_of_pos_left this (by positivity)
    have h4 : μ / β * (β / μ * (c * x)) = x * c := by field_simp
    linarith
  set y : ℕ → ℝ := fun n => m (t0 + n) with hy
  have hyrec : ∀ n, y (n + 1) = g (y n) := fun n => by simp only [hy, ← add_assoc]; exact hrec _
  have hylow : ∀ n, mlow < y n := fun n => or_path_above_mlow hβ hμ hc hFneg hpath _
  have hstep : ∀ n, y n < ms ∧ y (n + 1) < y n := by
    intro n
    induction n with
    | zero => exact ⟨hcon, by rw [hyrec]; exact hdown _ (hylow 0).le hcon⟩
    | succ n ih =>
      have h1 : y (n + 1) < ms := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hyrec (n + 1)]; exact hdown _ (hylow _).le h1⟩
  have hanti : Antitone y := antitone_nat_of_succ_le fun n => (hstep n).2.le
  rcases antitone_orbit_atBot_or_fixed hyrec hanti with h | ⟨L, hL, hbd, hfixL⟩
  · obtain ⟨n, hn⟩ := (h.eventually (eventually_le_atBot mlow)).exists
    linarith [hylow n]
  · have hLlow : mlow ≤ L := ge_of_tendsto hL (Eventually.of_forall fun n => (hylow n).le)
    have hcL : ContinuousAt g L :=
      ((continuousAt_const.mul (hFc.continuousAt (Ioi_mem_nhds (by linarith))))).div
        continuousAt_const hc.ne'
    have hf := hfixL hcL
    have hLms : L < ms := lt_of_le_of_lt (hbd 0) (hstep 0).1
    have := hdown L hLlow hLms
    linarith

/-- Woodford (2003), (4.10), p. 136, the bounds of the Obstfeld–Rogoff iteration:
`m̲₀ = m̲`, `m̲_{k+1} = F⁻¹((β/μ̄)G(m̲_k))`. Under continuity, the single crossing below `m*` and
`m̲ < m*`, such a sequence exists, is nondecreasing, stays in `[m̲, m*]`, and converges to `m*`. -/
theorem or_bounds_exist {β μ c mlow ms : ℝ} {F : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hmlow : 0 < mlow) (hlt : mlow < ms) (hFc : ContinuousOn F (Set.Ioi 0))
    (hfix : F ms = β / μ * (c * ms))
    (hbelow : ∀ x, mlow ≤ x → x < ms → F x < β / μ * (c * x)) :
    ∃ b : ℕ → ℝ, b 0 = mlow ∧ (∀ k, F (b (k + 1)) = β / μ * (c * b k)) ∧ Monotone b ∧
      (∀ k, mlow ≤ b k ∧ b k ≤ ms) ∧ Tendsto b atTop (𝓝 ms) := by
  have hsucc : ∀ x : ℝ, ∃ y : ℝ, x ∈ Set.Icc mlow ms →
      y ∈ Set.Icc x ms ∧ F y = β / μ * (c * x) := by
    intro x
    by_cases hx : x ∈ Set.Icc mlow ms
    · rcases hx.2.lt_or_eq with hlt' | heq
      · have hlo : F x ≤ β / μ * (c * x) := (hbelow x hx.1 hlt').le
        have hhi : β / μ * (c * x) ≤ F ms := by
          rw [hfix]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2 hc.le) (by positivity)
        obtain ⟨y, hy, hFy⟩ := intermediate_value_Icc hx.2
          (hFc.mono fun z hz => (by linarith [hz.1, hx.1] : (0 : ℝ) < z)) ⟨hlo, hhi⟩
        exact ⟨y, fun _ => ⟨hy, hFy⟩⟩
      · exact ⟨ms, fun _ => ⟨⟨heq.le, le_rfl⟩, by rw [hfix, heq]⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hsucc
  set b : ℕ → ℝ := fun k => g^[k] mlow with hb
  have hbs : ∀ k, b (k + 1) = g (b k) := fun k => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ k, b k ∈ Set.Icc mlow ms := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hlt.le⟩
    | succ n ih =>
      rw [hbs]
      have := (hg _ ih).1
      exact ⟨le_trans ih.1 this.1, this.2⟩
  have hmono : Monotone b := monotone_nat_of_le_succ fun k => by
    rw [hbs]; exact (hg _ (hmem k)).1.1
  have hF : ∀ k, F (b (k + 1)) = β / μ * (c * b k) := fun k => by
    rw [hbs]; exact (hg _ (hmem k)).2
  refine ⟨b, rfl, hF, hmono, fun k => hmem k, ?_⟩
  have hbdd : BddAbove (Set.range b) := ⟨ms, by rintro _ ⟨k, rfl⟩; exact (hmem k).2⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ k, b k with hL
  have hLms : L ≤ ms := ciSup_le fun k => (hmem k).2
  have hLlow : mlow ≤ L := le_trans (hmem 0).1 (le_ciSup hbdd 0)
  have hcL : ContinuousAt F L := hFc.continuousAt (Ioi_mem_nhds (by linarith))
  have h1 : Tendsto (fun k => F (b (k + 1))) atTop (𝓝 (F L)) :=
    hcL.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun k => F (b (k + 1))) atTop (𝓝 (β / μ * (c * L))) := by
    simp only [hF]
    exact (hlim.const_mul c).const_mul (β / μ)
  have hFL := tendsto_nhds_unique h1 h2
  rcases hLms.lt_or_eq with hlt' | heq
  · have := hbelow L hLlow hlt'
    linarith
  · rw [← heq]; exact hlim

/-- Woodford (2003), (4.10), p. 136, the iteration step "no perfect-foresight equilibrium can
ever have `m_t ≤ m̲₁ ≡ F⁻¹(β/μ̄ G(m̲))` … `m_t ≤ m̲₂` … and so on": if `F ≤ 0` on `(0, m̲]`, `F` is
strictly increasing on `[m̲, ∞)` and `b` is any sequence of bounds as in `or_bounds_exist`, every
path satisfies `m_t > b_k` for all `t` and `k`. -/
theorem or_iteration_bound {β μ c mlow : ℝ} {F : ℝ → ℝ} {m b : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0) (hFmono : StrictMonoOn F (Set.Ici mlow))
    (hb0 : b 0 = mlow) (hbF : ∀ k, F (b (k + 1)) = β / μ * (c * b k)) (hblow : ∀ k, mlow ≤ b k)
    (hpath : IsORPath β μ c F m) : ∀ k t, b k < m t := by
  intro k
  induction k with
  | zero => intro t; rw [hb0]; exact or_path_above_mlow hβ hμ hc hFneg hpath t
  | succ k ih =>
    intro t
    by_contra hcon
    push Not at hcon
    have hmt := or_path_above_mlow hβ hμ hc hFneg hpath t
    have h1 : F (m t) ≤ F (b (k + 1)) :=
      hFmono.monotoneOn (Set.mem_Ici.mpr hmt.le) (Set.mem_Ici.mpr (hblow _)) hcon
    rw [hbF] at h1
    have h2 : F (m t) = β / μ * (c * m (t + 1)) := by
      rw [hpath.2 t]; field_simp
    rw [h2] at h1
    have h3 : c * m (t + 1) ≤ c * b k := le_of_mul_le_mul_left h1 (by positivity)
    have h4 := ih (t + 1)
    nlinarith

/-- Woodford (2003), (4.10), p. 136, conclusion of the Obstfeld–Rogoff iteration: under the
hypotheses of `or_bounds_exist` and `or_iteration_bound` every perfect-foresight path satisfies
`m_t ≥ m*` at all dates — no self-fulfilling inflation. -/
theorem or_paths_above_mstar {β μ c mlow ms : ℝ} {F : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hμ : 0 < μ) (hc : 0 < c) (hmlow : 0 < mlow) (hlt : mlow < ms)
    (hFc : ContinuousOn F (Set.Ioi 0)) (hfix : F ms = β / μ * (c * ms))
    (hbelow : ∀ x, mlow ≤ x → x < ms → F x < β / μ * (c * x))
    (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0) (hFmono : StrictMonoOn F (Set.Ici mlow))
    (hpath : IsORPath β μ c F m) : ∀ t, ms ≤ m t := by
  obtain ⟨b, hb0, hbF, -, hbI, hlim⟩ := or_bounds_exist hβ hμ hc hmlow hlt hFc hfix hbelow
  have hbd := or_iteration_bound hβ hμ hc hFneg hFmono hb0 hbF (fun k => (hbI k).1) hpath
  intro t
  exact le_of_tendsto' hlim fun k => (hbd k t).le

end Woodford.PriceLevelDetermination.MoneyTargetingDynamics
