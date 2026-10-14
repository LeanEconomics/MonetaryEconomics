/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.ForwardSolution
import PriceLevelDetermination.LogLinear

/-!
# A Wicksellian policy regime

Woodford (2003), *Interest and Prices*, Chapter 2, §1.2, eqs. (1.29)–(1.39), pp. 74–85, and the
linear core of Proposition 2.3 (p. 82; proof in Appendix A, §A.4, pp. 635–636).

## Main results

* `taxes_1_29`: the implied tax rule (1.29) follows EXACTLY from the government flow constraint
  (1.25), the riskless-debt payoff and (1.5) (so survey item E14 is not an error).
* `steadyState_fisher`, `steadyState_rate_pos`, `steadyState_tvc`: the steady state of p. 79
  (`P_t = P*_t`, `i = ī = (π̄ − β)/β > 0`) satisfies (1.21), and (1.24) holds along it.
* `identity_1_35`, `system_iff_reduced`: (1.32) + (1.34) + (1.35) ⇔ (1.36).
* `priceGap` (1.37), `existsUnique_priceGap`, `prop_2_3_linear`: for `φ_p > 0` (more generally
  `|1 + φ_p| > 1`) and bounded `{r̂, π*, ν}` (`r̂`, `ν` adapted), (1.37) is the unique bounded
  solution of (1.36); `interest_1_38`: the matching nominal rate (1.38);
  `determinate_iff`: for `φ_p ≥ 0`, determinacy holds iff `φ_p > 0`.
* `logPrice_1_39`, `weights_hasSum_one`, `weights_pos`: the representation (1.39) of `log P_t`
  as a weighted average with positive weights summing to one.
* Footnote 17 (survey error E1): `fn17_corrected` — the equilibrium log price depends on
  `(P*, ν)` only through `log P* − φ_p⁻¹ ν`; `fn17_printed_false` — the printed combination
  `log P* − (φ_p⁻¹ + 1)ν` does not determine it.
* p. 85: `zero_gap_iff` (with constant `P*`, `P̂ ≡ 0 ⇔ ν ≡ r̂`); `abs_priceGap_le` (the effect of
  the gap `r̂ − ν` is at most `sup|r̂ − ν|/φ_p`), `gap_bound_antitone`, `gap_bound_tendsto_zero`,
  `constant_gap` (the bound is attained); footnote 20: `gibson`.
-/

namespace Woodford.PriceLevelDetermination.Wicksell

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The fiscal rule (1.29) -/

/-- Woodford (2003), eq. (1.29), p. 76: with riskless one-period debt, the implied taxes are
`T_{t+1} = (1 + i_t)(D_t − Δ_t M_t) − D_{t+1}`, where `Δ_t = (i_t − i^m_t)/(1 + i_t)`. This
follows exactly from the government flow constraint (1.25)
`E_t[Q_{t,t+1} W_{t+1}] = W_t − T_t − Δ_t M_t`, the payoff
`W_{t+1} = (1 + i^m_t) M_t + (1 + i_t) B_t` known at `t`, `D = M + B`, and (1.5)
`E_t Q_{t,t+1} = (1 + i_t)⁻¹` (pull-out of the known payoff). -/
theorem taxes_1_29 (hPO : 𝔼.PullOut) {i im M B D T W Q Δ : ℕ → Ω → ℝ}
    (hi : ∀ t ω, 1 + i t ω ≠ 0) (hD : ∀ t ω, D t ω = M t ω + B t ω)
    (hΔ : ∀ t ω, Δ t ω = (i t ω - im t ω) / (1 + i t ω))
    (hW : ∀ t ω, W (t + 1) ω = (1 + im t ω) * M t ω + (1 + i t ω) * B t ω)
    (hWk : ∀ t, 𝔼.E t (W (t + 1)) = W (t + 1))
    (hQ : ∀ t ω, 𝔼.E t (Q (t + 1)) ω = (1 + i t ω)⁻¹)
    (hgov : ∀ t ω, 𝔼.E t (Q (t + 1) * W (t + 1)) ω = W t ω - T t ω - Δ t ω * M t ω) (t : ℕ)
    (ω : Ω) : T (t + 1) ω = (1 + i t ω) * (D t ω - Δ t ω * M t ω) - D (t + 1) ω := by
  have hWD : ∀ s ω, W (s + 1) ω = (1 + i s ω) * (D s ω - Δ s ω * M s ω) := by
    intro s ω
    rw [hW, hD, hΔ]
    field_simp [hi s ω]
    ring
  have hpo := congrFun (hPO (t + 1) (W (t + 2)) (Q (t + 2)) (hWk (t + 1))) ω
  have hg := hgov (t + 1) ω
  rw [mul_comm (Q (t + 2)) (W (t + 2)), hpo] at hg
  simp only [Pi.mul_apply] at hg
  rw [hQ (t + 1) ω, hWD (t + 1) ω] at hg
  have h1 : (1 + i (t + 1) ω) * (D (t + 1) ω - Δ (t + 1) ω * M (t + 1) ω) *
      (1 + i (t + 1) ω)⁻¹ = D (t + 1) ω - Δ (t + 1) ω * M (t + 1) ω := by
    field_simp [hi (t + 1) ω]
  rw [h1] at hg
  rw [← hWD t ω]
  linarith

/-! ### The steady state (p. 79) -/

/-- Woodford (2003), p. 79: along the steady state `Y = Ȳ`, `ξ = 0` (so `u_c ≡ ū > 0`),
`P_t = P*_t = P_0 π̄ᵗ` and `i_t = ī = (π̄ − β)/β`, the exact Fisher equation (1.21) holds. -/
theorem steadyState_fisher {β pibar ubar P0 : ℝ} (hβ : 0 < β) (hpi : 0 < pibar)
    (hu : 0 < ubar) (hP0 : 0 < P0) (t : ℕ) :
    LogLinear.FisherExact 𝔼 β (fun _ _ => (pibar - β) / β) (fun _ _ => ubar)
      (fun s _ => P0 * pibar ^ s) t := by
  intro ω
  have hfun : (fun (_ : Ω) => ubar * (P0 * pibar ^ t) / (ubar * (P0 * pibar ^ (t + 1)))) =
      fun _ => pibar⁻¹ := by
    funext
    rw [pow_succ]
    field_simp
  dsimp only
  rw [hfun, 𝔼.const]
  field_simp
  ring

/-- Woodford (2003), p. 79: the steady-state interest rate `ī = (π̄ − β)/β` is positive iff
`π̄ > β`, and `1 + φ(1; 0) = π̄/β` makes the rule consistent with it: `φ(1; 0) = ī`. -/
theorem steadyState_rate_pos {β pibar φ0 : ℝ} (hβ : 0 < β) (hφ : 1 + φ0 = pibar / β) :
    (0 < (pibar - β) / β ↔ β < pibar) ∧ φ0 = (pibar - β) / β := by
  refine ⟨⟨fun h => ?_, fun h => div_pos (by linarith) hβ⟩, ?_⟩
  · have := (div_pos_iff_of_pos_right hβ).mp h
    linarith
  · field_simp at hφ ⊢
    linarith

/-- Woodford (2003), p. 79 and (1.24): along the steady state with `D_T = D_0 γ_Dᵀ`,
`0 < γ_D < π̄/β` and `P_T = P_0 π̄ᵀ`, the transversality term `βᵀ ū D_T/P_T` tends to `0`. -/
theorem steadyState_tvc {β pibar γ ubar D0 P0 : ℝ} (hβ : 0 < β) (hpi : 0 < pibar)
    (hγ0 : 0 < γ) (hγ : γ < pibar / β) :
    Tendsto (fun T : ℕ => β ^ T * (ubar * (D0 * γ ^ T) / (P0 * pibar ^ T))) atTop (𝓝 0) := by
  have hr0 : 0 ≤ β * γ / pibar := by positivity
  have hr1 : β * γ / pibar < 1 := by
    rw [div_lt_one hpi]
    rw [lt_div_iff₀ hβ] at hγ
    linarith
  have heq : ∀ T : ℕ, β ^ T * (ubar * (D0 * γ ^ T) / (P0 * pibar ^ T)) =
      ubar * D0 / P0 * (β * γ / pibar) ^ T := by
    intro T
    rw [div_pow, mul_pow]
    field_simp
  simp_rw [heq]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (ubar * D0 / P0)

/-! ### The log-linear system (1.32), (1.34), (1.35) and (1.36) -/

/-- Woodford (2003), eq. (1.35), p. 81: with `P̂ = log P − log P*`,
`π_{t+1} = log P_{t+1} − log P_t` and `π*_{t+1} = log P*_{t+1} − log P*_t`,
`π_{t+1} = P̂_{t+1} − P̂_t + π*_{t+1}`. -/
theorem identity_1_35 (lp lps : ℕ → Ω → ℝ) (t : ℕ) :
    lp (t + 1) - lp t = (lp (t + 1) - lps (t + 1)) - (lp t - lps t) + (lps (t + 1) - lps t) := by
  abel

/-- Woodford (2003), eq. (1.36), p. 81:
`(1 + φ_p) P̂_t = E_t P̂_{t+1} + r̂_t + E_t π*_{t+1} − ν_t`. -/
def Reduced (φp : ℝ) (r pis ν Ph : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + φp) • Ph t = 𝔼.E t (Ph (t + 1)) + r t + 𝔼.E t (pis (t + 1)) - ν t

/-- Woodford (2003), eqs. (1.32), (1.34), (1.35), pp. 79–81: the Fisher equation
`î_t = r̂_t + E_t π_{t+1}` with the rule `î_t = φ_p P̂_t + ν_t` and the identity
`π_{t+1} = P̂_{t+1} − P̂_t + π*_{t+1}` substituted. -/
def System (φp : ℝ) (r pis ν Ph : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φp • Ph t + ν t = r t + 𝔼.E t (Ph (t + 1) - Ph t + pis (t + 1))

/-- Woodford (2003), eq. (1.36), p. 81: for an adapted `P̂`, the system (1.32), (1.34), (1.35)
holds iff (1.36) holds. -/
theorem system_iff_reduced {φp : ℝ} {r pis ν Ph : ℕ → Ω → ℝ} (hPa : 𝔼.Adapted Ph) :
    System 𝔼 φp r pis ν Ph ↔ Reduced 𝔼 φp r pis ν Ph := by
  refine forall_congr' fun t => ?_
  rw [map_add, map_sub, hPa t, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), App. A, p. 636: the forcing term `u_t = (1 + φ_p)⁻¹(r̂_t + E_t π*_{t+1} − ν_t)`
of (1.36) written as (A.14). -/
noncomputable def forcing (φp : ℝ) (r pis ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (1 + φp)⁻¹ • (r t + 𝔼.E t (pis (t + 1)) - ν t)

/-- Woodford (2003), App. A, p. 636: (1.36) is (A.14) with `z = P̂` and `a = (1 + φ_p)⁻¹`. -/
theorem reduced_iff_solves {φp : ℝ} (hφ : 1 + φp ≠ 0) {r pis ν Ph : ℕ → Ω → ℝ} :
    Reduced 𝔼 φp r pis ν Ph ↔
      ForwardSolution.Solves 𝔼 (1 + φp)⁻¹ (forcing 𝔼 φp r pis ν) Ph := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [forcing, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), App. A, p. 636: the forcing term is adapted when `r̂` and `ν` are. -/
theorem forcing_adapted {φp : ℝ} {r pis ν : ℕ → Ω → ℝ} (hra : 𝔼.Adapted r)
    (hνa : 𝔼.Adapted ν) : 𝔼.Adapted (forcing 𝔼 φp r pis ν) := by
  intro t
  simp only [forcing, map_smul, map_sub, map_add, hra t, hνa t, 𝔼.E_E_self]

/-- Woodford (2003), App. A, p. 636: the forcing term is bounded when `r̂`, `π*`, `ν` are. -/
theorem forcing_bounded {φp Mr Mp Mν : ℝ} {r pis ν : ℕ → Ω → ℝ} (hr : ∀ t ω, |r t ω| ≤ Mr)
    (hp : ∀ t ω, |pis t ω| ≤ Mp) (hν : ∀ t ω, |ν t ω| ≤ Mν) (t : ℕ) (ω : Ω) :
    |forcing 𝔼 φp r pis ν t ω| ≤ |(1 + φp)⁻¹| * (Mr + Mp + Mν) := by
  simp only [forcing, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 := 𝔼.abs_E_le (hp (t + 1)) t ω
  calc |r t ω + 𝔼.E t (pis (t + 1)) ω - ν t ω|
      ≤ |r t ω + 𝔼.E t (pis (t + 1)) ω| + |ν t ω| := abs_sub _ _
    _ ≤ |r t ω| + |𝔼.E t (pis (t + 1)) ω| + |ν t ω| := by gcongr; exact abs_add_le _ _
    _ ≤ Mr + Mp + Mν := by linarith [hr t ω, hν t ω]

/-! ### (1.37)–(1.38) and Proposition 2.3 (linear core) -/

/-- Woodford (2003), eq. (1.37), p. 81:
`P̂_t = ∑_{j ≥ 0} (1 + φ_p)^{−(j+1)} E_t(r̂_{t+j} + π*_{t+j+1} − ν_{t+j})`. -/
noncomputable def priceGap (φp : ℝ) (r pis ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, (1 + φp)⁻¹ ^ (j + 1) * 𝔼.E t (r (t + j) + pis (t + j + 1) - ν (t + j)) ω

/-- Woodford (2003), eqs. (1.37) and (A.16), pp. 81, 636: (1.37) is the forward sum (A.16) of
(1.36). -/
theorem priceGap_eq_forwardSeries (φp : ℝ) (r pis ν : ℕ → Ω → ℝ) :
    priceGap 𝔼 φp r pis ν = 𝔼.forwardSeries (1 + φp)⁻¹ (forcing 𝔼 φp r pis ν) := by
  funext t ω
  unfold priceGap ExpectationSystem.forwardSeries forcing
  refine tsum_congr fun j => ?_
  have h : 𝔼.E t ((1 + φp)⁻¹ • (r (t + j) + 𝔼.E (t + j) (pis (t + j + 1)) - ν (t + j))) =
      (1 + φp)⁻¹ • 𝔼.E t (r (t + j) + pis (t + j + 1) - ν (t + j)) := by
    rw [map_smul, map_sub, map_add, 𝔼.tower (Nat.le_add_right t j), map_sub, map_add]
  rw [h, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Woodford (2003), p. 81: `|1 + φ_p| > 1` makes `|(1 + φ_p)⁻¹| < 1`; in particular `φ_p > 0`
does. -/
theorem abs_inv_lt_one {φp : ℝ} (hφ : 1 < |1 + φp|) : |(1 + φp)⁻¹| < 1 := by
  rw [abs_inv]
  exact inv_lt_one_of_one_lt₀ hφ

/-- Woodford (2003), p. 81: `φ_p > 0` gives `|1 + φ_p| > 1`. -/
theorem one_lt_abs_of_pos {φp : ℝ} (hφ : 0 < φp) : 1 < |1 + φp| := by
  rw [abs_of_pos (by linarith)]
  linarith

/-- Woodford (2003), eq. (1.37), Proposition 2.3 (linear core), pp. 81–82, and §A.4: for
`|1 + φ_p| > 1` (in particular `φ_p > 0`) and bounded `{r̂, π*, ν}` with `r̂`, `ν` adapted,
(1.37) is a bounded adapted solution of (1.36), and every bounded solution of (1.36) is (1.37). -/
theorem existsUnique_priceGap {φp : ℝ} (hφ : 1 < |1 + φp|) {r pis ν : ℕ → Ω → ℝ}
    (hrb : BoundedProc r) (hpb : BoundedProc pis) (hνb : BoundedProc ν) (hra : 𝔼.Adapted r)
    (hνa : 𝔼.Adapted ν) :
    Reduced 𝔼 φp r pis ν (priceGap 𝔼 φp r pis ν) ∧ BoundedProc (priceGap 𝔼 φp r pis ν) ∧
      𝔼.Adapted (priceGap 𝔼 φp r pis ν) ∧
      ∀ Ph, BoundedProc Ph → Reduced 𝔼 φp r pis ν Ph → Ph = priceGap 𝔼 φp r pis ν := by
  obtain ⟨Mr, hr⟩ := hrb
  obtain ⟨Mp, hp⟩ := hpb
  obtain ⟨Mν, hν⟩ := hνb
  have ha := abs_inv_lt_one hφ
  have hne : 1 + φp ≠ 0 := by
    intro h
    rw [h, abs_zero] at hφ
    linarith
  have hu := forcing_bounded 𝔼 (φp := φp) hr hp hν
  have hua := forcing_adapted 𝔼 (φp := φp) (pis := pis) hra hνa
  rw [priceGap_eq_forwardSeries]
  refine ⟨(reduced_iff_solves 𝔼 hne).mpr (ForwardSolution.forwardSeries_solves_abs 𝔼 ha hu hua),
    ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hu,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hu, fun Ph hPb hP => ?_⟩
  exact ForwardSolution.eq_forwardSeries_abs 𝔼 ha hu hua ((reduced_iff_solves 𝔼 hne).mp hP) hPb

/-- Woodford (2003), Proposition 2.3 (linear core), p. 82: for `φ_p > 0` and bounded `{r̂, π*, ν}`
(`r̂`, `ν` adapted) there is exactly one bounded adapted `P̂` satisfying the log-linear system
(1.32), (1.34), (1.35); it is (1.37). -/
theorem prop_2_3_linear {φp : ℝ} (hφ : 0 < φp) {r pis ν : ℕ → Ω → ℝ} (hrb : BoundedProc r)
    (hpb : BoundedProc pis) (hνb : BoundedProc ν) (hra : 𝔼.Adapted r) (hνa : 𝔼.Adapted ν) :
    ∃! Ph, BoundedProc Ph ∧ 𝔼.Adapted Ph ∧ System 𝔼 φp r pis ν Ph := by
  obtain ⟨h1, h2, h3, h4⟩ := existsUnique_priceGap 𝔼 (one_lt_abs_of_pos hφ) hrb hpb hνb hra hνa
  exact ⟨_, ⟨h2, h3, (system_iff_reduced 𝔼 h3).mpr h1⟩,
    fun Ph hP => h4 Ph hP.1 ((system_iff_reduced 𝔼 hP.2.1).mp hP.2.2)⟩

/-- Woodford (2003), eq. (1.38), p. 81: the nominal rate `î_t = φ_p P̂_t + ν_t` in the equilibrium
(1.37) is `∑_{j ≥ 0} φ_p (1 + φ_p)^{−(j+1)} E_t(r̂_{t+j} + π*_{t+j+1} − ν_{t+j}) + ν_t`. -/
theorem interest_1_38 (φp : ℝ) (r pis ν : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    φp * priceGap 𝔼 φp r pis ν t ω + ν t ω =
      ∑' j, φp * (1 + φp)⁻¹ ^ (j + 1) * 𝔼.E t (r (t + j) + pis (t + j + 1) - ν (t + j)) ω +
        ν t ω := by
  unfold priceGap
  rw [← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  ring

/-- Woodford (2003), Proposition 2.3, p. 82 (necessity of `φ_p > 0` within the book's `φ_p ≥ 0`):
the log-linear system has a unique bounded solution for all bounded disturbances iff `φ_p > 0`.
For `φ_p = 0` both `P̂ ≡ 0` and `P̂ ≡ 1` solve (1.36) with zero disturbances. -/
theorem determinate_iff [Nonempty Ω] {φp : ℝ} (hφ : 0 ≤ φp) :
    (∀ r pis ν : ℕ → Ω → ℝ, BoundedProc r → BoundedProc pis → BoundedProc ν → 𝔼.Adapted r →
      𝔼.Adapted ν → ∃! Ph, BoundedProc Ph ∧ Reduced 𝔼 φp r pis ν Ph) ↔ 0 < φp := by
  constructor
  · intro h
    by_contra hc
    have h0 : φp = 0 := by linarith [not_lt.mp hc]
    subst h0
    have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
    obtain ⟨Ph, -, hu⟩ := h 0 0 0 hzb hzb hzb (fun t => map_zero _) (fun t => map_zero _)
    have e0 := hu 0 ⟨hzb, fun t => by simp⟩
    have e1 := hu (fun _ _ => 1) ⟨⟨1, fun _ _ => by simp⟩, fun t => by
      rw [𝔼.const]; funext; simp⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (e1.trans e0.symm) 0) ω
    simp at this
  · intro hφ r pis ν hrb hpb hνb hra hνa
    obtain ⟨h1, h2, -, h4⟩ :=
      existsUnique_priceGap 𝔼 (one_lt_abs_of_pos hφ) hrb hpb hνb hra hνa
    exact ⟨_, ⟨h2, h1⟩, fun Ph hP => h4 Ph hP.1 hP.2⟩

/-! ### The representation (1.39) -/

/-- Woodford (2003), eq. (1.39), p. 83: the weights `ϕ_j = φ_p (1 + φ_p)^{−(j+1)}` are positive. -/
theorem weights_pos {φp : ℝ} (hφ : 0 < φp) (j : ℕ) : 0 < φp * (1 + φp)⁻¹ ^ (j + 1) :=
  mul_pos hφ (pow_pos (inv_pos.mpr (by linarith)) _)

/-- Woodford (2003), eq. (1.39), p. 83: the weights `ϕ_j` sum to one. -/
theorem weights_hasSum_one {φp : ℝ} (hφ : 0 < φp) :
    HasSum (fun j : ℕ => φp * (1 + φp)⁻¹ ^ (j + 1)) 1 := by
  have hq0 : 0 ≤ (1 + φp)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (1 + φp)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (φp * (1 + φp)⁻¹))
  have hne : (1 : ℝ) + φp ≠ 0 := by linarith
  have h1 : 1 - (1 + φp)⁻¹ = φp * (1 + φp)⁻¹ := by
    have hinv : (1 + φp) * (1 + φp)⁻¹ = 1 := mul_inv_cancel₀ hne
    linear_combination (-1 : ℝ) * hinv
  have heq : φp * (1 + φp)⁻¹ * (1 - (1 + φp)⁻¹)⁻¹ = 1 := by
    rw [h1]
    exact mul_inv_cancel₀ (mul_ne_zero hφ.ne' (inv_ne_zero hne))
  rw [heq] at h
  convert h using 1
  funext j
  ring

/-- Woodford (2003), eq. (1.39), p. 83: with `log P = log P* + P̂` and `P̂` given by (1.37),
`log P_t = ∑_{j ≥ 0} ϕ_j E_t[log P*_{t+j} + φ_p⁻¹(r̂_{t+j} − ν_{t+j})]`,
`ϕ_j = φ_p (1 + φ_p)^{−(j+1)}`, for an adapted log target `log P*` with bounded growth
`π*_{t+1} = log P*_{t+1} − log P*_t` (summation by parts, survey lemma L2). -/
theorem logPrice_1_39 {φp Mr Mp Mν : ℝ} (hφ : 0 < φp) {lps r pis ν : ℕ → Ω → ℝ}
    (hpis : ∀ t, pis (t + 1) = lps (t + 1) - lps t) (hla : 𝔼.Adapted lps)
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hp : ∀ t ω, |pis t ω| ≤ Mp) (hν : ∀ t ω, |ν t ω| ≤ Mν)
    (t : ℕ) (ω : Ω) :
    lps t ω + priceGap 𝔼 φp r pis ν t ω =
      ∑' j, φp * (1 + φp)⁻¹ ^ (j + 1) *
        𝔼.E t (lps (t + j) + φp⁻¹ • (r (t + j) - ν (t + j))) ω := by
  set q := (1 + φp)⁻¹ with hq
  have hne : (1 : ℝ) + φp ≠ 0 := by linarith
  have hq0 : 0 ≤ q := inv_nonneg.mpr (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h1q : 1 - q = φp * q := by rw [hq]; field_simp; ring
  set X : ℕ → ℝ := fun j => 𝔼.E t (lps (t + j)) ω with hX
  set Y : ℕ → ℝ := fun j => 𝔼.E t (r (t + j) - ν (t + j)) ω with hY
  have hXd : ∀ k, X (k + 1) - X k = 𝔼.E t (pis (t + k + 1)) ω := by
    intro k
    simp only [hX]
    rw [hpis (t + k), map_sub, Pi.sub_apply, add_assoc]
  have hXb : ∀ k, |X (k + 1) - X k| ≤ Mp := fun k => by
    rw [hXd]
    exact 𝔼.abs_E_le (hp (t + k + 1)) t ω
  obtain ⟨hs1, hs2, hparts⟩ := ForwardSolution.tsum_weights_by_parts hq0 hq1 X hXb
  have hX0 : X 0 = lps t ω := by simp only [hX, add_zero, hla t]
  have hsY : Summable (fun j => q ^ (j + 1) * Y j) := by
    refine Summable.of_norm_bounded
      (((summable_geometric_of_lt_one hq0 hq1).mul_left q).mul_right (Mr + Mν)) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0, pow_succ, mul_comm (q ^ j) q]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := 𝔼.abs_E_le (fun ω' => (abs_sub (r (t + j) ω') (ν (t + j) ω')).trans
      (add_le_add (hr (t + j) ω') (hν (t + j) ω'))) t ω
    change |𝔼.E t (r (t + j) - ν (t + j)) ω| ≤ Mr + Mν
    exact this
  -- the left-hand side
  have hL : priceGap 𝔼 φp r pis ν t ω =
      ∑' j, (q ^ (j + 1) * Y j + q ^ (j + 1) * (X (j + 1) - X j)) := by
    unfold priceGap
    refine tsum_congr fun j => ?_
    rw [hXd j]
    simp only [hY, ← hq]
    rw [map_sub, map_add, map_sub]
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  -- the right-hand side
  have hR : ∑' j, φp * (1 + φp)⁻¹ ^ (j + 1) *
      𝔼.E t (lps (t + j) + φp⁻¹ • (r (t + j) - ν (t + j))) ω =
      ∑' j, ((1 - q) * q ^ j * X j + q ^ (j + 1) * Y j) := by
    refine tsum_congr fun j => ?_
    rw [map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hX, hY, ← hq]
    rw [h1q]
    field_simp
    ring
  rw [hL, hR, hsY.tsum_add hs2, hs1.tsum_add hsY, hparts, hX0]
  ring

/-! ### Footnote 17 (survey error E1) -/

/-- Woodford (2003), fn. 17, p. 84, CORRECTED (survey error E1): the equilibrium log price level
depends on the target `log P*` and the shift `ν` only through `log P* − φ_p⁻¹ ν`. If two
specifications `(log P*, ν)` and `(log P*', ν')` have the same `log P*_t − φ_p⁻¹ ν_t` at every
date, the bounded equilibria of (1.36) give the same `log P_t = log P*_t + P̂_t`. -/
theorem fn17_corrected {φp Mr Mp Mν Mp' Mν' : ℝ} (hφ : 0 < φp)
    {lps lps' r pis pis' ν ν' Ph Ph' : ℕ → Ω → ℝ}
    (hcomb : ∀ t ω, lps t ω - φp⁻¹ * ν t ω = lps' t ω - φp⁻¹ * ν' t ω)
    (hpis : ∀ t, pis (t + 1) = lps (t + 1) - lps t)
    (hpis' : ∀ t, pis' (t + 1) = lps' (t + 1) - lps' t) (hla : 𝔼.Adapted lps)
    (hla' : 𝔼.Adapted lps') (hra : 𝔼.Adapted r) (hνa : 𝔼.Adapted ν) (hνa' : 𝔼.Adapted ν')
    (hr : ∀ t ω, |r t ω| ≤ Mr) (hp : ∀ t ω, |pis t ω| ≤ Mp) (hν : ∀ t ω, |ν t ω| ≤ Mν)
    (hp' : ∀ t ω, |pis' t ω| ≤ Mp') (hν' : ∀ t ω, |ν' t ω| ≤ Mν')
    (hPb : BoundedProc Ph) (hP : Reduced 𝔼 φp r pis ν Ph)
    (hPb' : BoundedProc Ph') (hP' : Reduced 𝔼 φp r pis' ν' Ph') (t : ℕ) (ω : Ω) :
    lps t ω + Ph t ω = lps' t ω + Ph' t ω := by
  have e := (existsUnique_priceGap 𝔼 (one_lt_abs_of_pos hφ) ⟨Mr, hr⟩ ⟨Mp, hp⟩ ⟨Mν, hν⟩ hra
    hνa).2.2.2 Ph hPb hP
  have e' := (existsUnique_priceGap 𝔼 (one_lt_abs_of_pos hφ) ⟨Mr, hr⟩ ⟨Mp', hp'⟩ ⟨Mν', hν'⟩
    hra hνa').2.2.2 Ph' hPb' hP'
  rw [e, e', logPrice_1_39 𝔼 hφ hpis hla hr hp hν, logPrice_1_39 𝔼 hφ hpis' hla' hr hp' hν']
  refine tsum_congr fun j => ?_
  have hf : lps (t + j) + φp⁻¹ • (r (t + j) - ν (t + j)) =
      lps' (t + j) + φp⁻¹ • (r (t + j) - ν' (t + j)) := by
    funext ω'
    have := hcomb (t + j) ω'
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  rw [hf]

/-- Woodford (2003), fn. 17, p. 84, the PRINTED claim is false (survey error E1): with `φ_p = 1`,
`r̂ = 0`, the specifications `(log P*, ν) = (0, 0)` and `(2, 1)` have the same printed combination
`log P* − (φ_p⁻¹ + 1)ν = 0`, but their (unique bounded) equilibria give `log P ≡ 0` and
`log P ≡ 1`. -/
theorem fn17_printed_false :
    ((0 : ℝ) - (1⁻¹ + 1) * 0 = 2 - (1⁻¹ + 1) * 1) ∧
      ∀ Ph Ph' : ℕ → Ω → ℝ, BoundedProc Ph → BoundedProc Ph' → Reduced 𝔼 1 0 0 0 Ph →
        Reduced 𝔼 1 0 0 (fun _ _ => 1) Ph' → ∀ t ω, 0 + Ph t ω = 0 ∧ 2 + Ph' t ω = 1 := by
  refine ⟨by norm_num, fun Ph Ph' hPb hPb' hP hP' t ω => ?_⟩
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hcb : BoundedProc (fun _ _ => (1 : ℝ) : ℕ → Ω → ℝ) := ⟨1, fun _ _ => by simp⟩
  have hφ : (1 : ℝ) < |1 + 1| := by norm_num
  have e := (existsUnique_priceGap 𝔼 hφ hzb hzb hzb (fun t => map_zero _)
    (fun t => map_zero _)).2.2.2
  have e' := (existsUnique_priceGap 𝔼 hφ hzb hzb hcb (fun t => map_zero _)
    (fun t => 𝔼.const t 1)).2.2.2
  have h0 : Reduced 𝔼 1 0 0 0 (0 : ℕ → Ω → ℝ) := fun t => by simp
  have h1 : Reduced 𝔼 1 0 0 (fun _ _ => 1) (fun _ _ => -1) := fun t => by
    rw [𝔼.const]
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, map_zero, smul_eq_mul]
    norm_num
  have hP0 : Ph = 0 := (e Ph hPb hP).trans (e 0 hzb h0).symm
  have hP1 : Ph' = fun _ _ => -1 :=
    (e' Ph' hPb' hP').trans (e' _ ⟨1, fun _ _ => by simp⟩ h1).symm
  rw [hP0, hP1]
  norm_num

/-! ### Price stability and the response coefficient (p. 85, fn. 20) -/

/-- Woodford (2003), p. 85: with a constant target (`π* ≡ 0`) and `φ_p > 0`, the bounded
equilibrium has `P_t = P*` at all dates (`P̂ ≡ 0`) if and only if `ν_t = r̂_t` at all dates. -/
theorem zero_gap_iff {φp : ℝ} (hφ : 0 < φp) {r ν Ph : ℕ → Ω → ℝ} (hrb : BoundedProc r)
    (hνb : BoundedProc ν) (hra : 𝔼.Adapted r) (hνa : 𝔼.Adapted ν) (hPb : BoundedProc Ph)
    (hP : Reduced 𝔼 φp r 0 ν Ph) : Ph = 0 ↔ ν = r := by
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  constructor
  · intro h
    funext t ω
    have := congrFun (hP t) ω
    rw [h] at this
    simp only [Pi.zero_apply, smul_zero, map_zero, Pi.sub_apply, Pi.add_apply] at this
    linarith
  · intro h
    have e := (existsUnique_priceGap 𝔼 (one_lt_abs_of_pos hφ) hrb hzb hνb hra hνa).2.2.2
    have h0 : Reduced 𝔼 φp r 0 ν 0 := fun t => by
      rw [h]
      simp
    exact (e Ph hPb hP).trans (e 0 hzb h0).symm

/-- Woodford (2003), p. 51 and p. 85 (a-priori bound for forward equations; restated from the
Woodford Chapter 1 project): if `z` is bounded, `z_t = a E_t z_{t+1} + u_t` with `|a| < 1`, and
`|u_t| ≤ K`, then `|z_t| ≤ K/(1 − |a|)`. -/
theorem abs_le_of_forward {a M K : ℝ} (ha : |a| < 1) {z u : ℕ → Ω → ℝ}
    (hz : ForwardSolution.Solves 𝔼 a u z) (hM : ∀ t ω, |z t ω| ≤ M)
    (hK : ∀ t ω, |u t ω| ≤ K) (t : ℕ) (ω : Ω) : |z t ω| ≤ K / (1 - |a|) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK t ω)
  have h1 : 0 < 1 - |a| := by linarith
  have key : ∀ n : ℕ, ∀ s ω', |z s ω'| ≤ |a| ^ n * M + K / (1 - |a|) := by
    intro n
    induction n with
    | zero =>
      intro s ω'
      have := hM s ω'
      have : 0 ≤ K / (1 - |a|) := div_nonneg hK0 h1.le
      rw [pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro s ω'
      have hE := 𝔼.abs_E_le (fun ω'' => ih (s + 1) ω'') s ω'
      rw [hz s]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc |a * 𝔼.E s (z (s + 1)) ω' + u s ω'|
          ≤ |a| * |𝔼.E s (z (s + 1)) ω'| + |u s ω'| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |a| * (|a| ^ n * M + K / (1 - |a|)) + K := by
            gcongr
            exact hK s ω'
        _ = |a| ^ (n + 1) * M + K / (1 - |a|) := by
            field_simp
            ring
  have hlim : Tendsto (fun n : ℕ => |a| ^ n * M + K / (1 - |a|)) atTop
      (𝓝 (K / (1 - |a|))) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const M).add_const
      (K / (1 - |a|))
  exact ge_of_tendsto' hlim fun n => key n t ω

/-- Woodford (2003), p. 85: with a constant target (`π* ≡ 0`) and `φ_p > 0`, if the gap satisfies
`|r̂_t − ν_t| ≤ K`, then every bounded equilibrium has `|P̂_t| ≤ K/φ_p`: the effect of the gap on
`log P` varies inversely with `φ_p`. -/
theorem abs_priceGap_le {φp K : ℝ} (hφ : 0 < φp) {r ν Ph : ℕ → Ω → ℝ}
    (hK : ∀ t ω, |r t ω - ν t ω| ≤ K) (hPb : BoundedProc Ph) (hP : Reduced 𝔼 φp r 0 ν Ph)
    (t : ℕ) (ω : Ω) : |Ph t ω| ≤ K / φp := by
  obtain ⟨M, hM⟩ := hPb
  have hne : (1 : ℝ) + φp ≠ 0 := by linarith
  have ha := abs_inv_lt_one (one_lt_abs_of_pos hφ)
  have hq0 : 0 < (1 + φp)⁻¹ := inv_pos.mpr (by linarith)
  have hs := (reduced_iff_solves 𝔼 hne).mp hP
  have hu : ∀ t ω, |forcing 𝔼 φp r 0 ν t ω| ≤ (1 + φp)⁻¹ * K := by
    intro t ω
    simp only [forcing, Pi.zero_apply, map_zero, add_zero, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, abs_mul, abs_of_pos hq0]
    exact mul_le_mul_of_nonneg_left (hK t ω) hq0.le
  have := abs_le_of_forward 𝔼 ha hs hM hu t ω
  rw [abs_of_pos hq0] at this
  have he : (1 + φp)⁻¹ * K / (1 - (1 + φp)⁻¹) = K / φp := by
    have h1 : 1 - (1 + φp)⁻¹ = φp * (1 + φp)⁻¹ := by
      have hinv : (1 + φp) * (1 + φp)⁻¹ = 1 := mul_inv_cancel₀ hne
      linear_combination (-1 : ℝ) * hinv
    rw [h1, div_eq_div_iff (mul_ne_zero hφ.ne' hq0.ne') hφ.ne']
    ring
  rwa [he] at this

/-- Woodford (2003), p. 85: the bound `K/φ_p` is antitone in `φ_p > 0` ("varies inversely"). -/
theorem gap_bound_antitone {K : ℝ} (hK : 0 ≤ K) :
    AntitoneOn (fun φp : ℝ => K / φp) (Set.Ioi 0) := by
  intro x hx y _ hxy
  exact div_le_div_of_nonneg_left hK hx hxy

/-- Woodford (2003), p. 85: the effect of the gap can be made arbitrarily small by a large
enough `φ_p`: `K/φ_p → 0` as `φ_p → ∞`. -/
theorem gap_bound_tendsto_zero (K : ℝ) :
    Tendsto (fun φp : ℝ => K / φp) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

/-- Woodford (2003), p. 85: the bound is attained — for a constant gap `r̂_t − ν_t = κ` (and
constant target) the bounded equilibrium is `P̂ ≡ κ/φ_p`. -/
theorem constant_gap {φp κ : ℝ} (hφ : 0 < φp) {r ν Ph : ℕ → Ω → ℝ} (hrb : BoundedProc r)
    (hνb : BoundedProc ν) (hra : 𝔼.Adapted r) (hνa : 𝔼.Adapted ν)
    (hgap : ∀ t ω, r t ω - ν t ω = κ) (hPb : BoundedProc Ph) (hP : Reduced 𝔼 φp r 0 ν Ph) :
    Ph = fun _ _ => κ / φp := by
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have e := (existsUnique_priceGap 𝔼 (one_lt_abs_of_pos hφ) hrb hzb hνb hra hνa).2.2.2
  have hc : Reduced 𝔼 φp r 0 ν (fun _ _ => κ / φp) := fun t => by
    rw [𝔼.const]
    funext ω
    have hg := hgap t ω
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, map_zero,
      smul_eq_mul]
    have hφ0 : φp ≠ 0 := hφ.ne'
    field_simp
    linear_combination (-φp) * hg
  exact (e Ph hPb hP).trans (e _ ⟨|κ / φp|, fun _ _ => le_rfl⟩ hc).symm

/-- Woodford (2003), fn. 20, p. 85 (Gibson paradox): with `ν ≡ 0` the rule (1.34) makes the
nominal rate move one-for-one (scaled by `φ_p`) with the log price level relative to target,
`î_t = φ_p (log P_t − log P*_t)`, so the two co-move perfectly. -/
theorem gibson {φp : ℝ} {ih lp lps : ℕ → Ω → ℝ}
    (hrule : ∀ t, ih t = φp • (lp t - lps t) + (0 : ℕ → Ω → ℝ) t) (t : ℕ) :
    ih t = φp • (lp t - lps t) := by
  rw [hrule t, Pi.zero_apply, add_zero]

end Woodford.PriceLevelDetermination.Wicksell
