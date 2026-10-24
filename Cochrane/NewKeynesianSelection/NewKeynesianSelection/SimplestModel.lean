/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.FTPLSimple

/-!
# The simplest new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.1 "The simplest model",
eqs. (16.1)–(16.11) and Figure 16.1, pp. 363–366.

The model is `i_t = E_t π_{t+1}` (16.1), `i_t = φ π_t + u_t` (16.2) and
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` (16.3), the same equations as the simplest fiscal-theory model
(`FTPLSimple.RuleModel`). The new-Keynesian reading makes fiscal policy passive, so (16.3) only
determines surpluses; the remaining condition is (16.4) `E_t π_{t+1} = φ π_t + u_t`. Its
equilibria are indexed by `π_0` and a sunspot shock `δ` (16.5). Selection rules out paths whose
expectations explode.

The equilibrium notions used here: an *equilibrium* of (16.4) is an adapted inflation process
satisfying (16.4) at every date; it is *locally bounded* (the new-Keynesian selection) when it is
a bounded process. The model is *determinate* when for every bounded adapted disturbance there
is exactly one bounded equilibrium.

## Main results

* (16.1)–(16.4): `nk_iff` (eliminating `i_t`); `passive_163` and `nk_passive_iff` (with passive
  fiscal policy (16.3) imposes nothing); `nk_with_163_iff_ruleModel` (with an exogenous fiscal
  shock the equations are exactly the fiscal-theory model).
* (16.5): `nkSol`, `nkSol_solves`, `eq164_iff_165`, `eq_nkSol`, `nkSol_inj`,
  `equilibria_bijOn` — the equilibria are in bijection with the pairs `(π_0, δ)`.
* `|φ| < 1` (p. 364, stable but indeterminate): `expected_succ`, `expected_bounded`
  (`E_t π_{t+j}` bounded in `j`), `expected_const_converges` (converges for any initial value),
  `converges_needs_convergent_u` (for a general bounded disturbance only boundedness holds),
  `sunspot_expected` and `sunspot_fades`, `indeterminate_of_abs_lt_one` (uncountably many
  bounded equilibria), `coin_sunspot` (a genuinely random sunspot equilibrium).
* `|φ| > 1` (p. 364, (16.6)): `fwdSol`, `fwdSol_apply` (`π_t = −∑ φ^{−(j+1)} E_t u_{t+j}`),
  `eq164_unique`, `fwdSol_existsUnique` (the unique bounded equilibrium),
  `explodes_of_ne_fwdSol` (every other
  equilibrium has `|E_t π_{t+j}| → ∞`), `determinate_iff` (determinate iff `|φ| > 1`, so
  `φ < −1` works as well as `φ > 1`).
* AR(1) disturbances (pp. 364–365): `ar1Pi`, `ar1Pi_eq164`, `ar1Pi_adapted`,
  `ar1Pi_bounded`, `ar1_solution` ((16.9) `π_t = −u_t/(φ − η)`),
  `ar1_rate` ((16.11)), `ar1_law_1610` ((16.10)), `ar1_selection` ((16.7)), `irf_ar1`.
* (16.8), the Wicksellian rule: `WicksellModel`, `wicksell_iff`, `wicksell_existsUnique`,
  `wicksell_apply` (`p_t = p* − ∑ (1+φ_p)^{−(j+1)} E_t u_{t+j}`), `wicksell_determinate_iff`
  (iff `φ_p > 0` or `φ_p < −2`), `printed_wicksell_false` (survey error E4: the printed formula
  with `1 + φ` is not a solution).
* Figure 16.1 (`φ = 1.25`, `η = 0.8`): `fig161_values`, `fig161_reverts`.
-/

namespace Cochrane.NewKeynesianSelection.SimplestModel

open Filter Topology Innovation

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (16.1)–(16.4) -/

/-- Cochrane (2023), eqs. (16.1)–(16.2), p. 364: the Fisher equation `i_t = E_t π_{t+1}` and the
Taylor-type rule `i_t = φ π_t + u_t` at every date. -/
def NKModel (φ : ℝ) (u i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ i t = φ • π t + u t

/-- Cochrane (2023), eq. (16.4), p. 364: the single equilibrium condition
`E_t π_{t+1} = φ π_t + u_t`. -/
def Eq164 (φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + u t

/-- Cochrane (2023), eq. (16.4), p. 364 ("We then eliminate `i_t` from (16.1)–(16.2)"): the model
holds iff the rate is given by the rule and inflation satisfies (16.4). -/
theorem nk_iff {φ : ℝ} {u i π : ℕ → Ω → ℝ} :
    NKModel 𝔼 φ u i π ↔ (∀ t, i t = φ • π t + u t) ∧ Eq164 𝔼 φ u π := by
  constructor
  · intro h
    exact ⟨fun t => (h t).2, fun t => (h t).1.symm.trans (h t).2⟩
  · rintro ⟨hi, h⟩ t
    exact ⟨(hi t).trans (h t).symm, hi t⟩

/-- Cochrane (2023), eq. (16.3), p. 364 (passive fiscal policy: "(16.3) determines surpluses
`ε_{Σs,t+1}` for any unexpected inflation"): for every inflation process the passive fiscal shock
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` (`FTPLSimple.passiveShock`) is a shock and (16.3) holds with
it. -/
theorem passive_163 (π : ℕ → Ω → ℝ) :
    IsShock 𝔼 (FTPLSimple.passiveShock 𝔼 π) ∧
      ∀ t, innov 𝔼 t (π (t + 1)) = -FTPLSimple.passiveShock 𝔼 π (t + 1) := by
  refine ⟨FTPLSimple.passiveShock_isShock 𝔼 π, fun t => ?_⟩
  change _ = -(-innov 𝔼 t (π (t + 1)))
  rw [neg_neg]

/-- Cochrane (2023), p. 364 ("As (16.3) then does not influence the rest of the model ... we have
a single equilibrium condition (16.4)"): with passive fiscal policy, (16.1)–(16.3) hold iff
(16.1)–(16.2) hold. -/
theorem nk_passive_iff {φ : ℝ} {u i π : ℕ → Ω → ℝ} :
    (NKModel 𝔼 φ u i π ∧ ∀ t, innov 𝔼 t (π (t + 1)) = -FTPLSimple.passiveShock 𝔼 π (t + 1)) ↔
      NKModel 𝔼 φ u i π :=
  ⟨fun h => h.1, fun h => ⟨h, (passive_163 𝔼 π).2⟩⟩

/-- Cochrane (2023), p. 364 ("the same set of equations as the simplest fiscal theory of monetary
policy model from Sections 2.5 and 2.6"): with an exogenous fiscal shock `ε`, (16.1)–(16.3) are
exactly the fiscal-theory rule model (2.20)–(2.22). -/
theorem nk_with_163_iff_ruleModel {φ : ℝ} {u i ε π : ℕ → Ω → ℝ} :
    (NKModel 𝔼 φ u i π ∧ ∀ t, innov 𝔼 t (π (t + 1)) = -ε (t + 1)) ↔
      FTPLSimple.RuleModel 𝔼 φ i u ε π := by
  constructor
  · rintro ⟨h, h3⟩ t
    exact ⟨(h t).1, h3 t, (h t).2⟩
  · intro h
    exact ⟨fun t => ⟨(h t).1, (h t).2.2⟩, fun t => (h t).2.1⟩

/-! ### (16.5): the equilibria -/

/-- Cochrane (2023), eq. (16.5), p. 364: `π_0` given and `π_{t+1} = φ π_t + u_t + δ_{t+1}`. -/
def nkSol (φ : ℝ) (u δ : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => φ • nkSol φ u δ π0 t + u t + δ (t + 1)

/-- Cochrane (2023), eq. (16.5), p. 364: the family (16.5) is the fiscal-theory solution (2.25)
with the fiscal shock `ε_{Σs} = −δ`. -/
theorem nkSol_eq_ruleSol (φ : ℝ) (u δ : ℕ → Ω → ℝ) (π0 : Ω → ℝ) :
    nkSol φ u δ π0 = FTPLSimple.ruleSol φ u (fun t => -δ t) π0 := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    change φ • nkSol φ u δ π0 t + u t + δ (t + 1) =
      φ • FTPLSimple.ruleSol φ u (fun t => -δ t) π0 t + u t - -δ (t + 1)
    rw [ih, sub_neg_eq_add]

/-- Cochrane (2023), eq. (16.5), p. 364: the members of (16.5) are adapted. -/
theorem nkSol_adapted {φ : ℝ} {u δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hδ : IsShock 𝔼 δ) : 𝔼.Adapted (nkSol φ u δ π0) := by
  have hs : IsShock 𝔼 (fun t => -δ t) :=
    ⟨fun t => by rw [map_neg, hδ.1 t], fun t => by rw [map_neg, hδ.2 t, neg_zero]⟩
  rw [nkSol_eq_ruleSol]
  exact FTPLSimple.ruleSol_adapted 𝔼 h0 hu hs

/-- Cochrane (2023), eq. (16.5), p. 364: every member of (16.5), for any `π_0` and any shock `δ`
(`E_t δ_{t+1} = 0`), is an equilibrium of (16.4). -/
theorem nkSol_solves {φ : ℝ} {u δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hδ : IsShock 𝔼 δ) : Eq164 𝔼 φ u (nkSol φ u δ π0) := by
  intro t
  have ha := nkSol_adapted 𝔼 (φ := φ) h0 hu hδ
  change 𝔼.E t (φ • nkSol φ u δ π0 t + u t + δ (t + 1)) = _
  rw [map_add, map_add, map_smul, ha t, hu t, hδ.2 t, add_zero]

/-- Cochrane (2023), eq. (16.5), p. 364: an adapted process satisfies (16.4) iff
`π_{t+1} = φ π_t + u_t + δ_{t+1}` with `δ` its own innovation process. -/
theorem eq164_iff_165 {φ : ℝ} {u π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u) :
    Eq164 𝔼 φ u π ↔ ∀ t, π (t + 1) = φ • π t + u t + innovProc 𝔼 π (t + 1) := by
  constructor
  · intro h t
    rw [← h t]
    exact eq_E_add_innovProc 𝔼 hπ t
  · intro h t
    rw [h t, map_add, map_add, map_smul, hπ t, hu t]
    rw [show innovProc 𝔼 π (t + 1) = innov 𝔼 t (π (t + 1)) from rfl, E_innov_zero, add_zero]

/-- Cochrane (2023), eq. (16.5), p. 364 ("Multiple equilibria are indexed by arbitrary initial
inflation `π_0`, and by the arbitrary random variables or sunspots `δ_{t+1}`"): every equilibrium
is the member of (16.5) with its own `π_0` and its own innovations. -/
theorem eq_nkSol {φ : ℝ} {u π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (h : Eq164 𝔼 φ u π) : π = nkSol φ u (innovProc 𝔼 π) (π 0) := by
  have h' := (eq164_iff_165 𝔼 hπ hu).mp h
  funext t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [h' t, ih]
    rfl

/-- Cochrane (2023), eq. (16.5), p. 364: different indices give different equilibria: if two
members of (16.5) agree, their `π_0` and their sunspots `δ_{t+1}` agree. -/
theorem nkSol_inj {φ : ℝ} {u δ δ' : ℕ → Ω → ℝ} {π0 π0' : Ω → ℝ}
    (h : nkSol φ u δ π0 = nkSol φ u δ' π0') : π0 = π0' ∧ ∀ t, δ (t + 1) = δ' (t + 1) := by
  refine ⟨congrFun h 0, fun t => ?_⟩
  have h1 := congrFun h (t + 1)
  have h2 := congrFun h t
  change φ • nkSol φ u δ π0 t + u t + δ (t + 1) = φ • nkSol φ u δ' π0' t + u t + δ' (t + 1)
    at h1
  rw [h2] at h1
  exact add_left_cancel h1

/-- Cochrane (2023), eq. (16.5), p. 364: the equilibria of (16.4) are in bijection with the pairs
`(π_0, δ)` of a date-0 known initial inflation and a shock (normalised by `δ_0 = 0`). -/
theorem equilibria_bijOn (φ : ℝ) {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    Set.BijOn (fun p : (Ω → ℝ) × (ℕ → Ω → ℝ) => nkSol φ u p.2 p.1)
      {p | 𝔼.E 0 p.1 = p.1 ∧ IsShock 𝔼 p.2 ∧ p.2 0 = 0}
      {π | 𝔼.Adapted π ∧ Eq164 𝔼 φ u π} := by
  refine ⟨fun p hp => ⟨nkSol_adapted 𝔼 hp.1 hu hp.2.1, nkSol_solves 𝔼 hp.1 hu hp.2.1⟩,
    fun p hp q hq hpq => ?_, fun π hπ => ?_⟩
  · obtain ⟨h0, hδ⟩ := nkSol_inj hpq
    refine Prod.ext h0 (funext fun t => ?_)
    cases t with
    | zero => rw [hp.2.2, hq.2.2]
    | succ t => exact hδ t
  · refine ⟨(π 0, innovProc 𝔼 π), ⟨hπ.1 0, innovProc_isShock 𝔼 π, rfl⟩, ?_⟩
    exact (eq_nkSol 𝔼 hπ.1 hu hπ.2).symm

/-! ### Expected inflation -/

/-- Cochrane (2023), p. 364: expected inflation in an equilibrium of (16.4) obeys
`E_t π_{t+j+1} = φ E_t π_{t+j} + E_t u_{t+j}`. -/
theorem expected_succ {φ : ℝ} {u π : ℕ → Ω → ℝ} (h : Eq164 𝔼 φ u π) (t j : ℕ) :
    𝔼.E t (π (t + j + 1)) = φ • 𝔼.E t (π (t + j)) + 𝔼.E t (u (t + j)) := by
  rw [← 𝔼.tower (Nat.le_add_right t j), h (t + j), map_add, map_smul]

/-- Cochrane (2023), p. 364: the difference of two equilibria (same disturbance) is expected to
evolve as `E_t(π'_{t+j} − π_{t+j}) = φʲ (π'_t − π_t)`. -/
theorem sunspot_expected {φ : ℝ} {u π π' : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hπ' : 𝔼.Adapted π')
    (h : Eq164 𝔼 φ u π) (h' : Eq164 𝔼 φ u π') (t j : ℕ) :
    𝔼.E t (π' (t + j)) - 𝔼.E t (π (t + j)) = φ ^ j • (π' t - π t) := by
  induction j with
  | zero => rw [add_zero, hπ t, hπ' t, pow_zero, one_smul]
  | succ j ih =>
    rw [← add_assoc, expected_succ 𝔼 h, expected_succ 𝔼 h', pow_succ, mul_comm, ← smul_smul,
      ← ih, smul_sub]
    abel

/-- Cochrane (2023), p. 364 ("If `|φ| < 1`, this economy is stable. Expected inflation
`E_t π_{t+j}` converges going forward for any initial value"): with a constant disturbance
`u ≡ c` and `φ ≠ 1`, `E_t π_{t+j} − c/(1−φ) = φʲ (π_t − c/(1−φ))`, so for `|φ| < 1` expected
inflation converges to `c/(1 − φ)` from any initial value. -/
theorem expected_const_converges {φ c : ℝ} (hφ : |φ| < 1) {π : ℕ → Ω → ℝ}
    (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ (fun _ _ => c) π) (t : ℕ) (ω : Ω) :
    (∀ j, 𝔼.E t (π (t + j)) ω - c / (1 - φ) = φ ^ j * (π t ω - c / (1 - φ))) ∧
      Tendsto (fun j => 𝔼.E t (π (t + j)) ω) atTop (𝓝 (c / (1 - φ))) := by
  have h1 : 1 - φ ≠ 0 := by
    have := (abs_lt.mp hφ).2
    linarith
  have key : ∀ j, 𝔼.E t (π (t + j)) ω - c / (1 - φ) = φ ^ j * (π t ω - c / (1 - φ)) := by
    intro j
    induction j with
    | zero => rw [add_zero, hπ t, pow_zero, one_mul]
    | succ j ih =>
      rw [← add_assoc, expected_succ 𝔼 h, 𝔼.const]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : 𝔼.E t (π (t + j)) ω = φ ^ j * (π t ω - c / (1 - φ)) + c / (1 - φ) := by
        linarith
      rw [e, pow_succ]
      field_simp
      ring
  refine ⟨key, ?_⟩
  have hlim : Tendsto (fun j => φ ^ j * (π t ω - c / (1 - φ)) + c / (1 - φ)) atTop
      (𝓝 (0 * (π t ω - c / (1 - φ)) + c / (1 - φ))) :=
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const _).add_const _
  rw [zero_mul, zero_add] at hlim
  refine hlim.congr fun j => ?_
  linarith [key j]

/-- Cochrane (2023), p. 364 ("stable"): for `|φ| < 1` and a bounded disturbance `|u| ≤ M`,
expected inflation in any equilibrium stays bounded at every horizon,
`|E_t π_{t+j}| ≤ |π_t| + M/(1 − |φ|)`. -/
theorem expected_bounded {φ M : ℝ} (hφ : |φ| < 1) {u π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : ∀ t ω, |u t ω| ≤ M) (h : Eq164 𝔼 φ u π) (t j : ℕ) (ω : Ω) :
    |𝔼.E t (π (t + j)) ω| ≤ |π t ω| + M / (1 - |φ|) := by
  have h1 : 0 < 1 - |φ| := by linarith
  have hM : 0 ≤ M := (abs_nonneg _).trans (hu 0 ω)
  have hK : 0 ≤ M / (1 - |φ|) := div_nonneg hM h1.le
  have hKe : |φ| * (M / (1 - |φ|)) + M = M / (1 - |φ|) := by
    field_simp
    ring
  induction j with
  | zero => rw [add_zero, hπ t]; linarith
  | succ j ih =>
    rw [← add_assoc, expected_succ 𝔼 h, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hu' := 𝔼.abs_E_le (hu (t + j)) t ω
    calc |φ * 𝔼.E t (π (t + j)) ω + 𝔼.E t (u (t + j)) ω|
        ≤ |φ| * |𝔼.E t (π (t + j)) ω| + |𝔼.E t (u (t + j)) ω| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |φ| * (|π t ω| + M / (1 - |φ|)) + M := by gcongr
      _ ≤ |π t ω| + M / (1 - |φ|) := by
          nlinarith [abs_nonneg φ, abs_nonneg (π t ω)]

/-- Cochrane (2023), p. 364 (imprecision): "Expected inflation `E_t π_{t+j}` converges going
forward for any initial value" needs a convergent forecast path of the disturbance (e.g. constant,
`expected_const_converges`); for a general bounded disturbance only boundedness holds
(`expected_bounded`). Counterexample: perfect foresight, `φ = 0`, `u_t = (−1)ᵗ`: the equilibrium
`π_0 = 0`, `π_{t+1} = (−1)ᵗ` has `E_0 π_j = π_j` oscillating between `1` and `−1`. -/
theorem converges_needs_convergent_u :
    Eq164 perfectForesight 0 (fun t _ => (-1 : ℝ) ^ t) (nkSol 0 (fun t _ => (-1 : ℝ) ^ t) 0 0) ∧
      ¬ ∃ L, Tendsto (fun j => perfectForesight.E 0
        (nkSol 0 (fun t _ => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) atTop (𝓝 L) := by
  have hu : perfectForesight.Adapted (fun t (_ : Unit) => (-1 : ℝ) ^ t) := fun _ => rfl
  refine ⟨nkSol_solves perfectForesight rfl hu (isShock_zero _), ?_⟩
  rintro ⟨L, hL⟩
  have hval : ∀ k : ℕ, nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (k + 1) () = (-1) ^ k := by
    intro k
    change (0 : ℝ) • nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 k () + (-1) ^ k + 0 = _
    simp
  have h1 : Tendsto (fun k : ℕ => (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩)
  have h2 : Tendsto (fun k : ℕ => (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 2)) atTop (𝓝 L) :=
    hL.comp (tendsto_atTop_atTop_of_monotone (fun a b h => by omega) fun b => ⟨b, by omega⟩)
  have e1 : ∀ k : ℕ, (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 1) = 1 := by
    intro k
    change nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + (2 * k + 1)) () = 1
    rw [zero_add, hval, pow_mul]
    simp
  have e2 : ∀ k : ℕ, (fun j => perfectForesight.E 0
      (nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + j)) ()) (2 * k + 2) = -1 := by
    intro k
    change nkSol 0 (fun t (_ : Unit) => (-1 : ℝ) ^ t) 0 0 (0 + (2 * k + 1 + 1)) () = -1
    rw [zero_add, hval, pow_succ, pow_mul]
    simp
  simp only [e1] at h1
  simp only [e2] at h2
  have := tendsto_nhds_unique (tendsto_const_nhds.congr' (Eventually.of_forall fun _ => rfl)) h1
  have := (tendsto_nhds_unique tendsto_const_nhds h2).trans this.symm
  norm_num at this

/-- Cochrane (2023), p. 364 ("'Sunspot' shocks `δ_{t+1}` can erupt at any time, and fade
away"): for `|φ| < 1` the expected effect of any sunspot dies out: two equilibria satisfy
`E_t(π'_{t+j} − π_{t+j}) → 0`. -/
theorem sunspot_fades {φ : ℝ} (hφ : |φ| < 1) {u π π' : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hπ' : 𝔼.Adapted π') (h : Eq164 𝔼 φ u π) (h' : Eq164 𝔼 φ u π') (t : ℕ) (ω : Ω) :
    Tendsto (fun j => 𝔼.E t (π' (t + j)) ω - 𝔼.E t (π (t + j)) ω) atTop (𝓝 0) := by
  have e : (fun j => 𝔼.E t (π' (t + j)) ω - 𝔼.E t (π (t + j)) ω) =
      fun j => φ ^ j * (π' t ω - π t ω) := by
    funext j
    have := congrFun (sunspot_expected 𝔼 hπ hπ' h h' t j) ω
    simpa using this
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const (π' t ω - π t ω)

/-- Cochrane (2023), eq. (16.5), p. 364: for `|φ| < 1` and bounded `π_0`, disturbance and
sunspot, the member of (16.5) is bounded. -/
theorem nkSol_bounded {φ A Mu Md : ℝ} (hφ : |φ| < 1) {u δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (h0 : ∀ ω, |π0 ω| ≤ A) (hu : ∀ t ω, |u t ω| ≤ Mu) (hδ : ∀ t ω, |δ t ω| ≤ Md) :
    BoundedProc (nkSol φ u δ π0) := by
  rw [nkSol_eq_ruleSol]
  exact FTPLSimple.ruleSol_bounded hφ h0 hu (fun t ω => by simpa using hδ t ω)

/-- Cochrane (2023), p. 364 ("But it remains indeterminate"): for `|φ| < 1` and every bounded
adapted disturbance the bounded equilibria of (16.4) form an uncountable set (already `π_0` is
free). -/
theorem indeterminate_of_abs_lt_one [Nonempty Ω] {φ : ℝ} (hφ : |φ| < 1) {u : ℕ → Ω → ℝ}
    (hub : BoundedProc u) (hu : 𝔼.Adapted u) :
    ¬ {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ BoundedProc π ∧ Eq164 𝔼 φ u π}.Countable := by
  intro hc
  obtain ⟨M, hM⟩ := hub
  let f : ℝ → ℕ → Ω → ℝ := fun c => nkSol φ u 0 (fun _ => c)
  have hmaps : Set.MapsTo f Set.univ
      {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ BoundedProc π ∧ Eq164 𝔼 φ u π} := by
    intro c _
    refine ⟨nkSol_adapted 𝔼 (𝔼.const 0 c) hu (isShock_zero 𝔼),
      nkSol_bounded (A := |c|) (Md := 0) hφ (fun _ => le_rfl) hM (fun _ _ => by simp),
      nkSol_solves 𝔼 (𝔼.const 0 c) hu (isShock_zero 𝔼)⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    exact congrFun (congrFun h 0) ω
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-- Cochrane (2023), p. 364 (sunspots under genuine uncertainty): on the coin-flip event tree,
with `u = 0` and `π_0 = 0`, the coin shock is a sunspot: `nkSol φ 0 coinShock 0` is an adapted
equilibrium of (16.4) different from the zero equilibrium with the same `π_0`, and it is bounded
for `|φ| < 1`. -/
theorem coin_sunspot {φ : ℝ} (hφ : |φ| < 1) :
    let π := nkSol (Ω := Bool × Bool) φ 0 ExpectationsFiniteTree.coinShock 0
    ExpectationsFiniteTree.coinSystem.Adapted π ∧ Eq164 ExpectationsFiniteTree.coinSystem φ 0 π ∧
      BoundedProc π ∧ π 0 = 0 ∧ π ≠ 0 := by
  intro π
  have hs := (coin_shock_ne_zero).1
  have h0 : ExpectationsFiniteTree.coinSystem.E 0 (0 : Bool × Bool → ℝ) = 0 := map_zero _
  have hu : ExpectationsFiniteTree.coinSystem.Adapted (0 : ℕ → Bool × Bool → ℝ) :=
    fun t => map_zero _
  refine ⟨nkSol_adapted _ h0 hu hs, nkSol_solves _ h0 hu hs,
    nkSol_bounded (A := 0) (Mu := 0) (Md := 1) hφ (fun _ => by simp) (fun _ _ => by simp)
      (fun t ω => ?_), rfl, fun h => ?_⟩
  · unfold ExpectationsFiniteTree.coinShock
    split_ifs <;> simp
  · have := congrFun (congrFun h 1) (true, true)
    simp [π, nkSol, ExpectationsFiniteTree.coinShock] at this

/-! ### `|φ| > 1`: the locally bounded equilibrium (16.6) -/

/-- Cochrane (2023), p. 364: for `|φ| > 1`, (16.4) has at most one bounded solution (the
difference of two solutions solves `d_t = φ⁻¹ E_t d_{t+1}`); no bound or adaptedness of the
disturbance is needed. -/
theorem eq164_unique {φ : ℝ} (hφ : 1 < |φ|) {u π₁ π₂ : ℕ → Ω → ℝ} (h₁ : Eq164 𝔼 φ u π₁)
    (h₂ : Eq164 𝔼 φ u π₂) (hb₁ : BoundedProc π₁) (hb₂ : BoundedProc π₂) : π₁ = π₂ := by
  have hφ0 : φ ≠ 0 := fun h => by rw [h, abs_zero] at hφ; linarith
  have ha : |φ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hφ
  have key : ∀ π : ℕ → Ω → ℝ, Eq164 𝔼 φ u π →
      ∀ t, π t = φ⁻¹ • 𝔼.E t (π (t + 1)) + -(φ⁻¹ • u t) := by
    intro π h t
    rw [h t, smul_add, smul_smul, inv_mul_cancel₀ hφ0, one_smul]
    abel
  exact 𝔼.forward_unique ha (key π₁ h₁) (key π₂ h₂) hb₁ hb₂

/-- Cochrane (2023), eq. (16.4), p. 364: (16.4) is the undivided scalar equation
`φ π_t = E_t π_{t+1} − u_t` of the forward-solution module. -/
theorem eq164_iff_scalar (φ : ℝ) (u π : ℕ → Ω → ℝ) :
    Eq164 𝔼 φ u π ↔ ForwardSolution.ScalarEq 𝔼 φ 1 (fun t => -u t) π := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, one_mul]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eq. (16.6), p. 364: the forward solution
`π_t = −∑_{j ≥ 0} φ^{−(j+1)} E_t u_{t+j}`. -/
noncomputable def fwdSol (φ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  ForwardSolution.scalarSol 𝔼 φ 1 (fun t => -u t)

/-- Cochrane (2023), eq. (16.6), p. 364: `π_t = −∑_{j ≥ 0} (φ^{j+1})⁻¹ E_t u_{t+j}`. -/
theorem fwdSol_apply (φ : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    fwdSol 𝔼 φ u t ω = -∑' j, (φ ^ (j + 1))⁻¹ * 𝔼.E t (u (t + j)) ω := by
  rw [fwdSol, ForwardSolution.scalarSol_apply, ← tsum_neg]
  refine tsum_congr fun j => ?_
  simp only [one_pow, map_neg, Pi.neg_apply]
  ring

/-- Cochrane (2023), eq. (16.4), p. 364: for `φ ≠ 0` every solution of (16.4) with adapted
disturbance is adapted (`π_t = φ⁻¹(E_t π_{t+1} − u_t)`). -/
theorem eq164_adapted {φ : ℝ} (hφ : φ ≠ 0) {u π : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u)
    (h : Eq164 𝔼 φ u π) : 𝔼.Adapted π := by
  intro t
  have e : π t = φ⁻¹ • (𝔼.E t (π (t + 1)) - u t) := by
    rw [h t, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hφ, one_smul]
  rw [e, map_smul, map_sub, 𝔼.E_E_self, hu t]

/-- Cochrane (2023), eq. (16.6), p. 364 ("we find the unique locally-bounded equilibrium by
solving the difference equation (16.4) forward"): for `|φ| > 1` and a bounded adapted
disturbance, the forward solution is a bounded adapted equilibrium of (16.4), and every bounded
solution of (16.4) equals it. -/
theorem fwdSol_existsUnique {φ M : ℝ} (hφ : 1 < |φ|) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) :
    Eq164 𝔼 φ u (fwdSol 𝔼 φ u) ∧ BoundedProc (fwdSol 𝔼 φ u) ∧ 𝔼.Adapted (fwdSol 𝔼 φ u) ∧
      ∀ π, Eq164 𝔼 φ u π → BoundedProc π → π = fwdSol 𝔼 φ u := by
  have h1 : |(1 : ℝ)| < |φ| := by rwa [abs_one]
  have hf : ∀ t ω, |(fun t => -u t) t ω| ≤ M := fun t ω => by simpa using hM t ω
  have hfa : 𝔼.Adapted (fun t => -u t) := fun t => by simp only [map_neg, hu t]
  obtain ⟨hs, hb, ha, huniq⟩ := ForwardSolution.scalar_existsUnique 𝔼 h1 hf hfa
  exact ⟨(eq164_iff_scalar 𝔼 φ u _).mpr hs, hb, ha,
    fun π hπ hπb => huniq π ((eq164_iff_scalar 𝔼 φ u π).mp hπ) hπb⟩

/-- Cochrane (2023), p. 364 ("If `|φ| > 1`, all of these equilibria except one are expected
eventually to explode, i.e. `|E_t(π_{t+j})|` grows without bound"): for `|φ| > 1` and a bounded
adapted disturbance, every equilibrium other than (16.6) has, at some date and state,
`|E_t π_{t+j}| → ∞` as `j → ∞`. -/
theorem explodes_of_ne_fwdSol {φ M : ℝ} (hφ : 1 < |φ|) {u π : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) (hπ : 𝔼.Adapted π) (h : Eq164 𝔼 φ u π)
    (hne : π ≠ fwdSol 𝔼 φ u) :
    ∃ t ω, Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  obtain ⟨hs, ⟨K, hK⟩, ha, -⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
  have : ∃ t ω, π t ω ≠ fwdSol 𝔼 φ u t ω := by
    by_contra hc
    push Not at hc
    exact hne (funext fun t => funext fun ω => hc t ω)
  obtain ⟨t, ω, htω⟩ := this
  refine ⟨t, ω, ?_⟩
  have hd : 0 < |π t ω - fwdSol 𝔼 φ u t ω| := abs_pos.mpr (sub_ne_zero.mpr htω)
  have hlow : ∀ j, |φ| ^ j * |π t ω - fwdSol 𝔼 φ u t ω| + -K ≤ |𝔼.E t (π (t + j)) ω| := by
    intro j
    have e := congrFun (sunspot_expected 𝔼 ha hπ hs h t j) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    have hb := 𝔼.abs_E_le (hK (t + j)) t ω
    have h2 : |φ ^ j * (π t ω - fwdSol 𝔼 φ u t ω)| ≤
        |𝔼.E t (π (t + j)) ω| + |𝔼.E t (fwdSol 𝔼 φ u (t + j)) ω| := by
      rw [← e]
      exact abs_sub _ _
    rw [abs_mul, abs_pow] at h2
    linarith
  refine tendsto_atTop_mono hlow ?_
  exact tendsto_atTop_add_const_right _ _
    ((tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const hd)

/-- Cochrane (2023), p. 364 and p. 370 ("In this model `φ < −1` is as good as `φ > 1` to produce
local determinacy"): (16.4) has exactly one bounded equilibrium for every bounded adapted
disturbance if and only if `|φ| > 1`. -/
theorem determinate_iff [Nonempty Ω] (φ : ℝ) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∃! π, BoundedProc π ∧ Eq164 𝔼 φ u π) ↔
      1 < |φ| := by
  constructor
  · intro hdet
    by_contra hc
    push Not at hc
    have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
    obtain ⟨z, -, huniq⟩ := hdet 0 ⟨0, fun _ _ => by simp⟩ hz
    have e0 : Eq164 𝔼 φ 0 0 := fun t => by simp
    have e1 : Eq164 𝔼 φ 0 (fun t _ => φ ^ t) := fun t => by
      rw [𝔼.const]
      funext ω
      simp [pow_succ, mul_comm]
    have hb1 : BoundedProc (fun t (_ : Ω) => φ ^ t) :=
      ⟨1, fun t _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg φ) hc⟩
    have a := huniq 0 ⟨⟨0, fun _ _ => by simp⟩, e0⟩
    have b := huniq _ ⟨hb1, e1⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (b.trans a.symm) 0) ω
    simp at this
  · intro hφ u ⟨M, hM⟩ hu
    obtain ⟨hs, hb, -, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
    exact ⟨_, ⟨hb, hs⟩, fun π hπ => huniq π hπ.2 hπ.1⟩

/-! ### AR(1) disturbances, (16.7) and (16.9)–(16.11) -/

/-- Cochrane (2023), eq. (16.9), p. 365: the AR(1) inflation path `π_t = −u_t/(φ − η)`. -/
noncomputable def ar1Pi (φ η : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := (-(φ - η)⁻¹) • u t

/-- Cochrane (2023), eq. (16.9), p. 365: for an AR(1) disturbance (`E_t u_{t+1} = η u_t`) and
any `φ ≠ η`, `π_t = −u_t/(φ − η)` solves (16.4); no bound and no condition on `|φ|`. -/
theorem ar1Pi_eq164 {φ η : ℝ} (hφη : φ ≠ η) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) :
    Eq164 𝔼 φ u (ar1Pi φ η u) := by
  intro t
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  simp only [ar1Pi]
  rw [map_smul, hu.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), eq. (16.9), p. 365: the AR(1) path is adapted when `u` is. -/
theorem ar1Pi_adapted (φ η : ℝ) {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    𝔼.Adapted (ar1Pi φ η u) := fun t => by simp only [ar1Pi, map_smul, hu t]

/-- Cochrane (2023), eq. (16.9), p. 365: the AR(1) path is bounded when `u` is,
`|π_t| ≤ |(φ − η)⁻¹| M`. -/
theorem ar1Pi_bounded (φ η : ℝ) {M : ℝ} {u : ℕ → Ω → ℝ} (hM : ∀ t ω, |u t ω| ≤ M) :
    BoundedProc (ar1Pi φ η u) :=
  ⟨|(φ - η)⁻¹| * M, fun t ω => by
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)⟩

/-- Cochrane (2023), eq. (16.9), p. 365 (and p. 364): with an AR(1) disturbance
(`E_t u_{t+1} = η u_t`), bounded, `|φ| > 1` and `φ ≠ η`, the locally bounded equilibrium is
`π_t = −u_t/(φ − η)`. -/
theorem ar1_solution {φ η M : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.IsAR1 η u) :
    fwdSol 𝔼 φ u = ar1Pi φ η u := by
  obtain ⟨-, -, -, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM hu.1
  exact (huniq _ (ar1Pi_eq164 𝔼 hφη hu) (ar1Pi_bounded φ η hM)).symm

/-- Cochrane (2023), eq. (16.11), p. 365 (and p. 363): in the AR(1) equilibrium the interest
rate is `i_t = φ π_t + u_t = −η u_t/(φ − η)`. -/
theorem ar1_rate {φ η : ℝ} (hφη : φ ≠ η) (u : ℕ → Ω → ℝ) (t : ℕ) :
    φ • ((-(φ - η)⁻¹) • u t) + u t = (-(η / (φ - η))) • u t := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), eq. (16.10), p. 365: in the AR(1) equilibrium, with
`u_{t+1} = η u_t + ε_{i,t+1}`, inflation follows `π_{t+1} = η π_t − ε_{i,t+1}/(φ − η)`. -/
theorem ar1_law_1610 {φ η : ℝ} {u εi : ℕ → Ω → ℝ} (hlaw : AR1Law η u εi) (t : ℕ) :
    (-(φ - η)⁻¹) • u (t + 1) = η • ((-(φ - η)⁻¹) • u t) + (-(φ - η)⁻¹) • εi (t + 1) := by
  rw [hlaw t, smul_add, smul_smul, smul_smul, mul_comm]

/-- Cochrane (2023), eq. (16.7), p. 365 ("by this criterion we select the variables `π_0`,
`{δ_{t+1}}`"): in the AR(1) equilibrium, `π_0 = −u_0/(φ − η)` and the selected sunspot is
`δ_{t+1} = ΔE_{t+1} π_{t+1} = −ε_{t+1}/(φ − η)`, with `ε_{t+1} = u_{t+1} − η u_t`. -/
theorem ar1_selection {φ η M : ℝ} (hφ : 1 < |φ|) (hφη : φ ≠ η) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.IsAR1 η u) :
    fwdSol 𝔼 φ u 0 = (-(φ - η)⁻¹) • u 0 ∧
      ∀ t, innovProc 𝔼 (fwdSol 𝔼 φ u) (t + 1) = (-(φ - η)⁻¹) • (u (t + 1) - η • u t) := by
  rw [ar1_solution 𝔼 hφ hφη hM hu]
  refine ⟨rfl, fun t => ?_⟩
  change innov 𝔼 t ((-(φ - η)⁻¹) • u (t + 1)) = _
  rw [innov_smul, (shock_of_ar1 𝔼 hu).2.2 t]

/-- Cochrane (2023), Figure 16.1 and eqs. (16.9)–(16.11), p. 365: impulse responses of the AR(1)
equilibrium to a monetary-policy shock, as innovations: `ΔE_{t+1} u_{t+1+j} = ηʲ ε_{t+1}`,
`ΔE_{t+1} π_{t+1+j} = −ηʲ/(φ − η) ε_{t+1}` and `ΔE_{t+1} i_{t+1+j} = −η^{j+1}/(φ − η) ε_{t+1}`. -/
theorem irf_ar1 {φ η : ℝ} {u εi : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 εi)
    (hlaw : AR1Law η u εi) (t j : ℕ) :
    innov 𝔼 t (u (t + 1 + j)) = η ^ j • εi (t + 1) ∧
      innov 𝔼 t ((-(φ - η)⁻¹) • u (t + 1 + j)) = (-(η ^ j / (φ - η))) • εi (t + 1) ∧
      innov 𝔼 t ((-(η / (φ - η))) • u (t + 1 + j)) =
        (-(η ^ (j + 1) / (φ - η))) • εi (t + 1) := by
  have h := innov_ar1 𝔼 hu hε hlaw t j
  refine ⟨h, ?_, ?_⟩
  · rw [innov_smul, h, smul_smul]
    congr 1
    ring
  · rw [innov_smul, h, smul_smul]
    congr 1
    ring

/-! ### Figure 16.1 -/

/-- Cochrane (2023), Figure 16.1, p. 366 (`φ = 1.25`, `η = 0.8`): the responses to a unit
monetary shock are `π = −(0.8)ʲ/0.45` and `i = −(0.8)^{j+1}/0.45`; on impact inflation falls by
`20/9 ≈ 2.22` and the rate by `16/9 ≈ 1.78` percentage points. -/
theorem fig161_values (j : ℕ) :
    -(((4 : ℝ) / 5) ^ j / ((5 : ℝ) / 4 - 4 / 5)) = -(20 / 9) * ((4 : ℝ) / 5) ^ j ∧
      -(((4 : ℝ) / 5) ^ (j + 1) / ((5 : ℝ) / 4 - 4 / 5)) = -(16 / 9) * ((4 : ℝ) / 5) ^ j ∧
      -(((4 : ℝ) / 5) ^ 0 / ((5 : ℝ) / 4 - 4 / 5)) = -(20 / 9) := by
  refine ⟨by ring, by ring, by norm_num⟩

/-- Cochrane (2023), Figure 16.1, p. 365 ("In response to a positive shock to the disturbance
`u_t`, inflation `π_t` declines immediately, and then reverts slowly"): the inflation response
`−(20/9)(0.8)ʲ` is negative, strictly increasing in `j`, and tends to zero; the same holds for
the rate response `−(16/9)(0.8)ʲ`. -/
theorem fig161_reverts :
    (∀ j : ℕ, -(20 / 9) * ((4 : ℝ) / 5) ^ j < 0) ∧
      (∀ j : ℕ, -(20 / 9) * ((4 : ℝ) / 5) ^ j < -(20 / 9) * ((4 : ℝ) / 5) ^ (j + 1)) ∧
      Tendsto (fun j : ℕ => -(20 / 9) * ((4 : ℝ) / 5) ^ j) atTop (𝓝 0) ∧
      (∀ j : ℕ, -(16 / 9) * ((4 : ℝ) / 5) ^ j < -(16 / 9) * ((4 : ℝ) / 5) ^ (j + 1)) ∧
      Tendsto (fun j : ℕ => -(16 / 9) * ((4 : ℝ) / 5) ^ j) atTop (𝓝 0) := by
  have hp : ∀ j : ℕ, 0 < ((4 : ℝ) / 5) ^ j := fun j => by positivity
  have hl : Tendsto (fun j : ℕ => ((4 : ℝ) / 5) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨fun j => by nlinarith [hp j], fun j => ?_, by simpa using hl.const_mul (-(20 / 9)),
    fun j => ?_, by simpa using hl.const_mul (-(16 / 9))⟩
  · rw [pow_succ]; nlinarith [hp j]
  · rw [pow_succ]; nlinarith [hp j]

/-! ### (16.8): the Wicksellian rule -/

/-- Cochrane (2023), eq. (16.8), p. 365: the Fisher equation in the price level
`i_t = E_t p_{t+1} − p_t` and the Wicksellian rule `i_t = φ_p (p_t − p*) + u_t`. -/
def WicksellModel (φp pstar : ℝ) (u i p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (p (t + 1)) - p t ∧ i t = φp • (p t - fun _ => pstar) + u t

/-- Cochrane (2023), eq. (16.8), p. 365 ("substituting into the Fisher equation (16.1)"): for an
adapted price level, the model holds iff the rate follows the rule and the price gap
`x_t = p_t − p*` satisfies `E_t x_{t+1} = (1 + φ_p) x_t + u_t`. -/
theorem wicksell_iff {φp pstar : ℝ} {u i p : ℕ → Ω → ℝ} :
    WicksellModel 𝔼 φp pstar u i p ↔ (∀ t, i t = φp • (p t - fun _ => pstar) + u t) ∧
      Eq164 𝔼 (1 + φp) u (fun t => p t - fun _ => pstar) := by
  have hE : ∀ t, 𝔼.E t (p (t + 1) - fun _ => pstar) = 𝔼.E t (p (t + 1)) - fun _ => pstar :=
    fun t => by rw [map_sub, 𝔼.const]
  constructor
  · intro h
    refine ⟨fun t => (h t).2, fun t => ?_⟩
    rw [hE t]
    funext ω
    have a := congrFun (h t).1 ω
    have b := congrFun (h t).2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    linarith
  · rintro ⟨hi, h⟩ t
    refine ⟨?_, hi t⟩
    funext ω
    have a := congrFun (h t) ω
    have b := congrFun (hi t) ω
    rw [hE t] at a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    linarith

/-- Cochrane (2023), eq. (16.8), p. 365 ("if `φ_p > 0` and if we rule out explosive equilibria,
then we have a unique locally-bounded equilibrium price level"): for `|1 + φ_p| > 1` and a
bounded adapted disturbance, `p_t = p* + (forward solution of the gap)` is a bounded adapted
price level whose gap satisfies (16.8), and every bounded price level whose gap satisfies (16.8)
equals it. -/
theorem wicksell_existsUnique {φp pstar M : ℝ} (hφ : 1 < |1 + φp|) {u : ℕ → Ω → ℝ}
    (hM : ∀ t ω, |u t ω| ≤ M) (hu : 𝔼.Adapted u) :
    Eq164 𝔼 (1 + φp) u (fun t => (fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) - fun _ => pstar) ∧
      BoundedProc (fun t => fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) ∧
      𝔼.Adapted (fun t => fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) ∧
      ∀ q : ℕ → Ω → ℝ, Eq164 𝔼 (1 + φp) u (fun t => q t - fun _ => pstar) → BoundedProc q →
        q = fun t => fwdSol 𝔼 (1 + φp) u t + fun _ => pstar := by
  obtain ⟨hs, ⟨K, hK⟩, ha, huniq⟩ := fwdSol_existsUnique 𝔼 hφ hM hu
  have hgap : (fun t => (fwdSol 𝔼 (1 + φp) u t + fun _ => pstar) - fun _ => pstar) =
      fwdSol 𝔼 (1 + φp) u := by
    funext t
    exact add_sub_cancel_right _ _
  refine ⟨by rw [hgap]; exact hs, ⟨K + |pstar|, fun t ω => ?_⟩, fun t => ?_, fun q hq hqb => ?_⟩
  · simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hK t ω) le_rfl)
  · simp only [map_add, ha t, 𝔼.const]
  · obtain ⟨Q, hQ⟩ := hqb
    have hb : BoundedProc (fun t => q t - fun _ => pstar) := ⟨Q + |pstar|, fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hQ t ω) le_rfl)⟩
    have e := huniq _ hq hb
    funext t
    rw [← congrFun e t]
    exact (sub_add_cancel _ _).symm

/-- Cochrane (2023), p. 365 (the display after (16.8), with `φ_p` for the printed `φ`, survey
E4): the unique locally bounded price level is
`p_t = p* − ∑_{j ≥ 0} ((1 + φ_p)^{j+1})⁻¹ E_t u_{t+j}`. -/
theorem wicksell_apply (φp pstar : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    (fwdSol 𝔼 (1 + φp) u t + fun (_ : Ω) => pstar) ω =
      pstar - ∑' j, ((1 + φp) ^ (j + 1))⁻¹ * 𝔼.E t (u (t + j)) ω := by
  rw [Pi.add_apply, fwdSol_apply]
  ring

/-- Cochrane (2023), eq. (16.8), p. 365, and survey E4: the price gap `x = p − p*` is determinate
(exactly one bounded solution of `E_t x_{t+1} = (1 + φ_p) x_t + u_t` for every bounded adapted
disturbance) iff `φ_p > 0` or `φ_p < −2`. The book states only `φ_p > 0`. -/
theorem wicksell_determinate_iff [Nonempty Ω] (φp : ℝ) :
    (∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u →
      ∃! x, BoundedProc x ∧ Eq164 𝔼 (1 + φp) u x) ↔ (0 < φp ∨ φp < -2) := by
  rw [determinate_iff 𝔼 (1 + φp), lt_abs]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- Cochrane (2023), p. 365, survey error E4: the printed formula
`p_t = p* − ∑ (1 + φ)^{−(j+1)} E_t u_{t+j}` uses the inflation-rule coefficient `φ` instead of
`φ_p`. Counterexample under perfect foresight with `φ_p = 1`, `φ = 2`, `u ≡ 1`: the printed sum
is `∑ 3^{−(j+1)} = 1/2`, and the constant gap `−1/2` does not satisfy (16.8), while the corrected
gap `−∑ 2^{−(j+1)} = −1` does. -/
theorem printed_wicksell_false :
    (∑' j : ℕ, ((1 + (2 : ℝ)) ^ (j + 1))⁻¹ * 1 = 1 / 2) ∧
      (∑' j : ℕ, ((1 + (1 : ℝ)) ^ (j + 1))⁻¹ * 1 = 1) ∧
      ¬ Eq164 perfectForesight (1 + 1) (fun _ _ => 1) (fun _ _ => -(1 / 2 : ℝ)) ∧
      Eq164 perfectForesight (1 + 1) (fun _ _ => 1) (fun _ _ => -(1 : ℝ)) := by
  refine ⟨?_, ?_, fun h => ?_, fun t => ?_⟩
  · have h := ForwardSolution.tsum_geometric_ratio (A := 3) (B := 1) 1 (by norm_num)
    calc ∑' j : ℕ, ((1 + (2 : ℝ)) ^ (j + 1))⁻¹ * 1 = ∑' j : ℕ, (1 : ℝ) * 1 ^ j / 3 ^ (j + 1) :=
          tsum_congr fun j => by norm_num
      _ = 1 / (3 - 1) := h
      _ = 1 / 2 := by norm_num
  · have h := ForwardSolution.tsum_geometric_ratio (A := 2) (B := 1) 1 (by norm_num)
    calc ∑' j : ℕ, ((1 + (1 : ℝ)) ^ (j + 1))⁻¹ * 1 = ∑' j : ℕ, (1 : ℝ) * 1 ^ j / 2 ^ (j + 1) :=
          tsum_congr fun j => by norm_num
      _ = 1 / (2 - 1) := h
      _ = 1 := by norm_num
  · have := congrFun (h 0) ()
    norm_num [perfectForesight] at this
  · funext ω
    norm_num [perfectForesight]

end Cochrane.NewKeynesianSelection.SimplestModel
