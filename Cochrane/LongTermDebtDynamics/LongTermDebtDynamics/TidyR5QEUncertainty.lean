/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.QuantitativeEasing
import LongTermDebtDynamics.ExpectationsFiniteTree

/-!
# Quantitative easing with a separate Treasury and Fed, under uncertainty

Cochrane (2023), §7.6.1, pp. 229–232, equations (7.22)–(7.24).

In the book the path after the date-0 shock is perfect foresight ("I drop `E_0` in front of
`1/P_j`", p. 230), and "for a desired price-level path and a choice of one of monetary `M` or QE
purchases `B̃`, (7.23) gives us the other one". Here surpluses and price levels are random. The
Treasury keeps the geometric structure `ϖ^{j−t} B`, the QE purchases `B̃_0^{(j)}` are fixed at
date 0, and reserves `M_{t−1}^{(t)}` are chosen at `t − 1` (predetermined). At every `t ≥ 1` the
present-value relation is
`M_{t−1}^{(t)}/P_t + ∑_{j≥t} β^{j−t}(ϖ^{j−t}B + B̃_0^{(j)}) E_t(1/P_j) = E_t ∑_k β^k s_{t+k}`
(`QEPV`).

* `qe_iff`: given the price process, (7.23) determines the reserves state by state,
  `M_{t−1}^{(t)} = (E_t ∑ β^k s_{t+k} − V_t) P_t` with `V_t` the value of Treasury and QE bonds.
* `reserves_exist_iff`: **the reverse engineering under uncertainty.** Predetermined reserves
  supporting a given random price path exist (and are then unique, `reserves_unique`) if and only
  if `R_t = (E_t ∑ β^k s_{t+k} − V_t) P_t` is known at `t − 1` for every `t ≥ 1`. Under perfect
  foresight the condition is automatic, which is the book's statement
  (`perfectForesight_reserves_exist`).
* `innovation_form`: the content of (7.23) under uncertainty is an innovation restriction:
  `M_{t−1}^{(t)}(1/P_t − E_{t−1}(1/P_t)) = (news in the present value of surpluses) −
  (news in the value of Treasury and QE bonds)`. The central bank sets the expected path;
  fiscal news sets the surprises.
* `no_reserves_of_news`, `coin_no_reserves`: a price path known one period ahead (a
  deterministic one, say) cannot be supported when the present value of surpluses has news:
  with a coin-flip surplus shock and a deterministic desired price path there are no
  predetermined reserves at all.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): the present-value relation at `t` with
Treasury debt `ϖ^{j−t} B`, QE bonds `B̃_0^{(j)} = b j`, reserves `M_{t−1}^{(t)} = Mr t`:
`∑_k β^k (ϖ^k B + B̃_0^{(t+k)}) E_t(1/P_{t+k}) = E_t ∑_k β^k s_{t+k} − M_{t−1}^{(t)}/P_t`. -/
def QEPV (β om B : ℝ) (b Mr x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) * 𝔼.E t (x (t + k)) ω))
    (pvSurplus 𝔼 β s t ω - Mr t ω * x t ω)

/-- Cochrane (2023), §7.6.1, p. 230: the reserves implied by (7.23) at `t`,
`R_t = (E_t ∑ β^k s_{t+k} − V_t)/(1/P_t)`, where `V_t` is the value of Treasury and QE bonds. -/
noncomputable def resv (β : ℝ) (V x s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (pvSurplus 𝔼 β s t ω - V t ω) / x t ω

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): with `V_t` the (convergent) value of
Treasury and QE bonds and `1/P_t > 0`, the present-value relation at `t` holds if and only if the
reserves are `R_t`. -/
theorem qe_iff {β om B : ℝ} {b Mr x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (hx : ∀ t ω, 0 < x t ω) (t : ℕ) :
    QEPV 𝔼 β om B b Mr x s t ↔ Mr t = resv 𝔼 β V x s t := by
  constructor
  · intro h
    funext ω
    have := (h ω).unique (hV t ω)
    rw [resv, eq_div_iff (hx t ω).ne']
    linarith
  · intro h ω
    convert hV t ω using 1
    rw [h, resv]
    field_simp [(hx t ω).ne']
    ring

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): the reserves supporting a given random
price path, if any, are unique at every date `t ≥ 1`. -/
theorem reserves_unique {β om B : ℝ} {b Mr Mr' x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (hx : ∀ t ω, 0 < x t ω) (t : ℕ)
    (h : QEPV 𝔼 β om B b Mr x s t) (h' : QEPV 𝔼 β om B b Mr' x s t) : Mr t = Mr' t := by
  rw [(qe_iff 𝔼 hV hx t).mp h, (qe_iff 𝔼 hV hx t).mp h']

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): **reverse engineering of reserves.**
Given a random price path (`1/P > 0`) and the QE purchases, there are predetermined reserves
(`M_{t}^{(t+1)}` known at `t`) satisfying the present-value relation at every date `t ≥ 1` if
and only if the implied reserves `R_{t+1}` are known at `t` for every `t`. -/
theorem reserves_exist_iff {β om B : ℝ} {b x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (hx : ∀ t ω, 0 < x t ω) :
    (∃ Mr : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (Mr (t + 1)) = Mr (t + 1)) ∧
      ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) ↔
      ∀ t, 𝔼.E t (resv 𝔼 β V x s (t + 1)) = resv 𝔼 β V x s (t + 1) := by
  constructor
  · rintro ⟨Mr, hMr, hpv⟩ t
    rw [← (qe_iff 𝔼 hV hx (t + 1)).mp (hpv t)]
    exact hMr t
  · intro hR
    refine ⟨resv 𝔼 β V x s, hR, fun t => (qe_iff 𝔼 hV hx (t + 1)).mpr rfl⟩

/-- Cochrane (2023), §7.6.1, p. 230: **under perfect foresight (the book's case) the reserves
always exist**: for any positive price path and QE purchases, `M_{t−1}^{(t)} = R_t` satisfies
(7.23) at every `t ≥ 1`. -/
theorem perfectForesight_reserves_exist {β om B : ℝ} {b x s V : ℕ → Unit → ℝ}
    (hV : ∀ t u, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) u) *
      perfectForesight.E t (x (t + k)) u)) (V t u)) (hx : ∀ t u, 0 < x t u) :
    ∃ Mr : ℕ → Unit → ℝ, (∀ t, perfectForesight.E t (Mr (t + 1)) = Mr (t + 1)) ∧
      ∀ t, QEPV perfectForesight β om B b Mr x s (t + 1) :=
  (reserves_exist_iff perfectForesight hV hx).mpr fun _ => rfl

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): **the innovation form.** With
predetermined reserves, `M_{t}^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1}))` equals the news in the present
value of surpluses minus the news in the value of Treasury and QE bonds. -/
theorem innovation_form (hpo : 𝔼.PullOut) {β om B : ℝ} {b Mr x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (t : ℕ) (hMr : 𝔼.E t (Mr (t + 1)) = Mr (t + 1))
    (h : QEPV 𝔼 β om B b Mr x s (t + 1)) :
    Mr (t + 1) * (x (t + 1) - 𝔼.E t (x (t + 1))) =
      (pvSurplus 𝔼 β s (t + 1) - 𝔼.E t (pvSurplus 𝔼 β s (t + 1))) -
        (V (t + 1) - 𝔼.E t (V (t + 1))) := by
  have hlev : Mr (t + 1) * x (t + 1) = pvSurplus 𝔼 β s (t + 1) - V (t + 1) := by
    funext ω
    have := (h ω).unique (hV (t + 1) ω)
    simp only [Pi.mul_apply, Pi.sub_apply]
    linarith
  have hE : Mr (t + 1) * 𝔼.E t (x (t + 1)) =
      𝔼.E t (pvSurplus 𝔼 β s (t + 1)) - 𝔼.E t (V (t + 1)) := by
    rw [← hpo t _ _ hMr, hlev, map_sub]
  rw [mul_sub, hlev, hE]
  ring

/-- Cochrane (2023), §7.6.1 (under uncertainty): **a price path known one period ahead cannot be
supported when the present value of surpluses has news.** If `1/P_{t+1}` and the bond value
`V_{t+1}` are known at `t` but `E_{t+1} ∑ β^k s_{t+1+k}` is not, no predetermined reserves satisfy
the present-value relation at `t + 1`. -/
theorem no_reserves_of_news (hpo : 𝔼.PullOut) {β om B : ℝ} {b x s V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + b (t + k) ω) *
      𝔼.E t (x (t + k)) ω)) (V t ω)) (t : ℕ) (hxk : 𝔼.E t (x (t + 1)) = x (t + 1))
    (hVk : 𝔼.E t (V (t + 1)) = V (t + 1))
    (hnews : 𝔼.E t (pvSurplus 𝔼 β s (t + 1)) ≠ pvSurplus 𝔼 β s (t + 1)) :
    ¬ ∃ Mr : ℕ → Ω → ℝ, 𝔼.E t (Mr (t + 1)) = Mr (t + 1) ∧ QEPV 𝔼 β om B b Mr x s (t + 1) := by
  rintro ⟨Mr, hMr, h⟩
  have := innovation_form 𝔼 hpo hV t hMr h
  rw [hxk, sub_self, mul_zero, hVk, sub_self, sub_zero] at this
  exact hnews (sub_eq_zero.mp this.symm).symm

/-! ### A coin-flip surplus shock -/

/-- Cochrane (2023), §7.6.1 (illustration under uncertainty): surpluses `s_t = 1`, except a
fair coin-flip shock `±1` added at date 1 (revealed at date 1). -/
noncomputable def coinS : ℕ → Bool × Bool → ℝ :=
  fun t ω => 1 + if t = 1 then ExpectationsFiniteTree.coinShock 1 ω else 0

/-- Cochrane (2023), §7.6.1 (illustration): the present value of surpluses at date 1 is
`1/(1−β) + ε_1`, which carries the date-1 news `ε_1`. -/
theorem coin_pv {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ω : Bool × Bool) :
    pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 ω =
      1 / (1 - β) + ExpectationsFiniteTree.coinShock 1 ω := by
  have hk1 : ExpectationsFiniteTree.coinSystem.E 1 (ExpectationsFiniteTree.coinShock 1) ω =
      ExpectationsFiniteTree.coinShock 1 ω := by
    rw [ExpectationsFiniteTree.coinSystem,
      ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
      ExpectationsFiniteTree.coinShock_measurable 1 h
  have hterm : ∀ k, surplusTerm ExpectationsFiniteTree.coinSystem β coinS 1 k ω =
      β ^ k * 1 + (Pi.single 0 (ExpectationsFiniteTree.coinShock 1 ω) : ℕ → ℝ) k := by
    intro k
    rcases k with _ | k
    · have hf : coinS (1 + 0) = (fun _ => (1 : ℝ)) + ExpectationsFiniteTree.coinShock 1 := by
        funext ω'; simp [coinS]
      simp only [surplusTerm, hf, map_add, ExpectationsFiniteTree.coinSystem.const, Pi.add_apply,
        hk1, pow_zero, one_mul, Pi.single_eq_same]
    · have hf : coinS (1 + (k + 1)) = fun _ => (1 : ℝ) := by
        funext ω'; simp [coinS]
      simp only [surplusTerm, hf, ExpectationsFiniteTree.coinSystem.const,
        Pi.single_eq_of_ne (show k + 1 ≠ 0 by omega), add_zero]
  have hs : HasSum (fun k => surplusTerm ExpectationsFiniteTree.coinSystem β coinS 1 k ω)
      (1 / (1 - β) + ExpectationsFiniteTree.coinShock 1 ω) := by
    simp only [hterm]
    have h := ((hasSum_geometric_of_lt_one hβ0 hβ1).mul_right 1).add
      (hasSum_pi_single 0 (ExpectationsFiniteTree.coinShock 1 ω))
    convert h using 1
    rw [mul_one, one_div]
  exact hs.tsum_eq

/-- Cochrane (2023), §7.6.1 (under uncertainty): **no reserves support a deterministic price path
when surpluses carry news.** In the coin-flip economy (`0 ≤ β < 1`), for any deterministic
path `1/P_t = p_t`, deterministic QE purchases and Treasury structure with a convergent
bond value, no reserves chosen at date 0 satisfy the present-value relation at date 1. -/
theorem coin_no_reserves {β om B : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (p bq : ℕ → ℝ) {v : ℝ}
    (hv : HasSum (fun k : ℕ => β ^ k * ((om ^ k * B + bq (1 + k)) * p (1 + k))) v) :
    ¬ ∃ Mr : ℕ → Bool × Bool → ℝ, ExpectationsFiniteTree.coinSystem.E 0 (Mr 1) = Mr 1 ∧
      QEPV ExpectationsFiniteTree.coinSystem β om B (fun j _ => bq j) Mr (fun t _ => p t)
        coinS 1 := by
  rintro ⟨Mr, hMr, h⟩
  have hc : ∀ (t : ℕ) (c : ℝ), ExpectationsFiniteTree.coinSystem.E t (fun _ => c) = fun _ => c :=
    fun t c => ExpectationsFiniteTree.coinSystem.const t c
  -- the relation at date 1 pins the present value of surpluses to a date-0 known variable
  have hlev : ∀ ω, pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 ω = v + Mr 1 ω * p 1 := by
    intro ω
    have h1 := h ω
    simp only [hc] at h1
    have := h1.unique hv
    linarith
  have hfun : pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 =
      (fun _ => v) + p 1 • Mr 1 := by
    funext ω; rw [hlev ω]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hknown : ExpectationsFiniteTree.coinSystem.E 0
      (pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1) =
      pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 := by
    rw [hfun, map_add, map_smul, hc, hMr]
  -- but its date-0 forecast is `1/(1−β)` while its value after heads is `1/(1−β) + 1`
  have hpvfun : pvSurplus ExpectationsFiniteTree.coinSystem β coinS 1 =
      (fun _ => 1 / (1 - β)) + ExpectationsFiniteTree.coinShock 1 := by
    funext ω; rw [coin_pv hβ0 hβ1 ω]; rfl
  have hE0 := ExpectationsFiniteTree.coinShock_mean_zero 0
  rw [zero_add] at hE0
  rw [hpvfun, map_add, hc, hE0] at hknown
  have := congrFun hknown (true, true)
  simp [ExpectationsFiniteTree.coinShock] at this

end Cochrane.LongTermDebtDynamics.TidyR5QEUncertainty
