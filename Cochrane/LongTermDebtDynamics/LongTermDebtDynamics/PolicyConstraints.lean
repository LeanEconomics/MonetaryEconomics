/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.GeneralFormula
import LongTermDebtDynamics.ExpectationsFiniteTree

/-!
# Constraints on policy

Cochrane (2023), §7.5, pp. 226–229, equations (7.18)–(7.21).

The present-value relation at date 0, (7.18),
`∑_j β^j B_{−1}^{(j)} E_0(1/P_j) = E_0 ∑_j β^j s_j`, is the only restriction that surplus-neutral
debt policy places on the sequence `{E_0(1/P_j)}`.

## Main results

* `DivClosed`, `perfectForesight_divClosed`, `finiteTree_divClosed`: quotients of known variables
  are known (true for perfect foresight and for every finite event tree); needed to state the
  policy (7.19), `B_0^{(j)} = E_0 s_j / E_0(1/P_j)`.
* `polOne_*` — **Theorem P, existence** via (7.19): for any positive targets `E_0(1/P_j)`
  consistent with (7.18), selling `B_0^{(j)} = E_0 s_j / E_0(1/P_j)` at date 0 and never trading
  again satisfies every flow and present-value relation, achieves the targets, and gives positive
  price levels.
* `polTwo_*` — the second policy (7.20): buy back the long-term debt at date 0 and roll over
  one-period debt with `B_{j−1}^{(j)}/P_j = E_j ∑ β^k s_{j+k}`; it achieves the same targets.
* `policies_differ`: many debt policies support the same price-level path.
* `presentValue_zero_nominal`: conversely every equilibrium satisfies (7.18).
* `onePeriod_price_zero`: with only one-period debt outstanding, `P_0` is independent of the
  future price levels.
* `qe_tradeoff`, `qe_tradeoff_strict`: with nonnegative positions `B_{−1}^{(j)} ≥ 0`, debt policy
  cannot raise some price levels without lowering others; `qe_negative_position` shows the
  nonnegativity hypothesis is needed (E7.8).
* `offset_shock`, `offset_shock_cost`: debt policy can absorb a fiscal shock at date 0, but only at
  the cost of higher future price levels.
* `end_of_period_value` — (7.21): the real end-of-period value of debt equals
  `E_0 ∑_{j≥1} β^j s_j`, whatever the quantities `B_0^{(j)}`.
-/

namespace Cochrane.LongTermDebtDynamics.PolicyConstraints

open Filter Topology MaturityStructure

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.5, p. 227: quotients of variables known at `t` are known at `t` (the
measurability fact needed to write the policy (7.19)). Like `PullOut`, it is not implied by the
`ExpectationSystem` axioms, so results that use it take it as a hypothesis. -/
def DivClosed : Prop :=
  ∀ t (f g : Ω → ℝ), 𝔼.E t f = f → 𝔼.E t g = g → 𝔼.E t (f / g) = f / g

/-- Cochrane (2023), §7.5: perfect foresight is closed under quotients. -/
theorem perfectForesight_divClosed : DivClosed perfectForesight := fun _ _ _ _ _ => rfl

/-- Cochrane (2023), §7.5: every finite event tree is closed under quotients (a quotient of
variables constant on information cells is constant on them). -/
theorem finiteTree_divClosed {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) : DivClosed T.toExpectationSystem := by
  intro t f g hf hg
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hf hg ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have h1 : f ω' = f ω := by
    rw [← congrFun hf ω', ← congrFun hf ω]; exact T.condE_congr f h
  have h2 : g ω' = g ω := by
    rw [← congrFun hg ω', ← congrFun hg ω]; exact T.condE_congr g h
  simp only [Pi.div_apply, h1, h2]

/-- Cochrane (2023), §7.5: `E_t(f/b) = E_t(f)/b` for `b` known at `t`. -/
theorem E_div_known (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {t : ℕ} {b : Ω → ℝ}
    (hb : 𝔼.E t b = b) (f : Ω → ℝ) : 𝔼.E t (f / b) = 𝔼.E t f / b := by
  have h1 : 𝔼.E t (1 / b) = 1 / b := hdc t 1 b (𝔼.const t 1) hb
  have : f / b = (1 / b) * f := by funext ω; simp [div_eq_inv_mul]
  rw [this, hpo t _ _ h1]
  funext ω
  simp [div_eq_inv_mul]

/-! ### Theorem P: the first policy (7.19) -/

/-- Cochrane (2023), eq. (7.19), p. 227: the date-0 sales `B_0^{(j)} = E_0 s_j / E_0(1/P_j)` for
targets `e_j = E_0(1/P_j)`. -/
noncomputable def bOne (s e : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ := 𝔼.E 0 (s j) / e j

/-- Cochrane (2023), eq. (7.19), p. 227: the debt policy: inherit `B_{−1}`, sell up to
`B_0^{(j)} = bOne j` at date 0, then never trade. -/
noncomputable def polOneD (D0 : ℕ → Ω → ℝ) (s e : ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ :=
  if t = 0 then D0 m else bOne 𝔼 s e m

/-- Cochrane (2023), eq. (7.19), p. 227: the resulting price levels, `1/P_0 = e_0` and
`1/P_j = s_j / B_0^{(j)}` (eq. (7.9)). -/
noncomputable def polOneX (s e : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  if t = 0 then e 0 else s t / bOne 𝔼 s e t

/-- Cochrane (2023), §7.5, p. 227: the standing hypotheses of Theorem P: positive surpluses after
date 0 with positive date-0 expectations, positive targets known at date 0, and the targets
consistent with the present-value relation (7.18). -/
def Targets (β : ℝ) (D0 : ℕ → Ω → ℝ) (s e : ℕ → Ω → ℝ) : Prop :=
  (∀ m, 𝔼.E 0 (D0 m) = D0 m) ∧ (∀ j, 𝔼.E 0 (e j) = e j) ∧ (∀ j ω, 0 < e j ω) ∧
    (∀ j ω, 0 < s (j + 1) ω) ∧ (∀ j ω, 0 < 𝔼.E 0 (s (j + 1)) ω) ∧
    ∀ ω, HasSum (fun j => β ^ j * (D0 j ω * e j ω)) (pvSurplus 𝔼 β s 0 ω)

/-- Cochrane (2023), eq. (7.20), p. 227: one-period debt `B_{j−1}^{(j)} = E_0 PV_j / e_j` with
`PV_j = E_j ∑_k β^k s_{j+k}`. -/
noncomputable def cTwo (β : ℝ) (s e : ℕ → Ω → ℝ) (j : ℕ) : Ω → ℝ :=
  𝔼.E 0 (pvSurplus 𝔼 β s j) / e j

/-- Cochrane (2023), eq. (7.20), p. 227: the second policy: buy back all long-term debt at date 0
and roll over one-period debt. -/
noncomputable def polTwoD (β : ℝ) (D0 : ℕ → Ω → ℝ) (s e : ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ :=
  if t = 0 then D0 m else if m = t then cTwo 𝔼 β s e m else 0

/-- Cochrane (2023), eq. (7.20), p. 227: the price levels, `B_{j−1}^{(j)}/P_j = E_j ∑ β^k s_{j+k}`.
-/
noncomputable def polTwoX (β : ℝ) (s e : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  if t = 0 then e 0 else pvSurplus 𝔼 β s t / cTwo 𝔼 β s e t

variable {𝔼}

/-- Cochrane (2023), eq. (7.19), p. 227: the date-0 sales are known at every date. -/
theorem bOne_known (hdc : DivClosed 𝔼) {s e : ℕ → Ω → ℝ} (he : ∀ j, 𝔼.E 0 (e j) = e j)
    (j t : ℕ) : 𝔼.E t (bOne 𝔼 s e j) = bOne 𝔼 s e j :=
  ForwardSolution.E_of_known 𝔼 (Nat.zero_le t) (hdc 0 _ _ (𝔼.E_E_self 0 _) (he j))

/-- Cochrane (2023), eq. (7.19), p. 227: the date-0 sales are positive. -/
theorem bOne_pos {β : ℝ} {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e)
    (j : ℕ) (ω : Ω) : 0 < bOne 𝔼 s e (j + 1) ω :=
  div_pos (hT.2.2.2.2.1 j ω) (hT.2.2.1 (j + 1) ω)

/-- Cochrane (2023), eq. (7.19), p. 227: the policy is predetermined. -/
theorem polOne_predetermined (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ}
    (hT : Targets 𝔼 β D0 s e) : Predetermined 𝔼 (polOneD 𝔼 D0 s e) := by
  refine ⟨fun m => ?_, fun t m => ?_⟩
  · simp only [polOneD, ↓reduceIte]; exact hT.1 m
  · simp only [polOneD, Nat.add_one_ne_zero, ↓reduceIte]
    exact bOne_known hdc hT.2.1 m t

/-- Cochrane (2023), eqs. (7.9), (7.19), p. 227: `E_t(1/P_{j+1}) = E_t s_{j+1} / B_0^{(j+1)}` for
every `t`; in particular the policy achieves the targets `E_0(1/P_j) = e_j`. -/
theorem polOne_E (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ}
    {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e) (t j : ℕ) :
    𝔼.E t (polOneX 𝔼 s e (j + 1)) = 𝔼.E t (s (j + 1)) / bOne 𝔼 s e (j + 1) := by
  simp only [polOneX, Nat.add_one_ne_zero, ↓reduceIte]
  exact E_div_known 𝔼 hpo hdc (bOne_known hdc hT.2.1 _ t) _

/-- Cochrane (2023), §7.5, p. 227 (Theorem P): **the policy achieves every target**,
`E_0(1/P_j) = e_j` for all `j`, including `1/P_0 = e_0`. -/
theorem polOne_achieves (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ}
    {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e) (j : ℕ) :
    𝔼.E 0 (polOneX 𝔼 s e j) = e j := by
  rcases j with _ | j
  · simp only [polOneX, ↓reduceIte]; exact hT.2.1 0
  · rw [polOne_E hpo hdc hT]
    funext ω
    simp only [bOne, Pi.div_apply]
    have h1 := hT.2.2.2.2.1 j ω
    have h2 := hT.2.2.1 (j + 1) ω
    field_simp

/-- Cochrane (2023), eq. (7.19), p. 227: `B_0^{(j)} E_0(1/P_j) = E_0 s_j`. -/
theorem polOne_719 (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β : ℝ} {D0 : ℕ → Ω → ℝ}
    {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e) (j : ℕ) :
    polOneD 𝔼 D0 s e 1 (j + 1) * 𝔼.E 0 (polOneX 𝔼 s e (j + 1)) = 𝔼.E 0 (s (j + 1)) := by
  rw [polOne_achieves hpo hdc hT]
  funext ω
  simp only [polOneD, one_ne_zero, ↓reduceIte, bOne, Pi.mul_apply, Pi.div_apply]
  have := hT.2.2.1 (j + 1) ω
  field_simp

/-- Cochrane (2023), §7.5, p. 227 (Theorem P): the price levels are positive. -/
theorem polOne_pos {β : ℝ} {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hT : Targets 𝔼 β D0 s e)
    (t : ℕ) (ω : Ω) : 0 < polOneX 𝔼 s e t ω := by
  rcases t with _ | j
  · simp only [polOneX, ↓reduceIte]; exact hT.2.2.1 0 ω
  · simp only [polOneX, Nat.add_one_ne_zero, ↓reduceIte, Pi.div_apply]
    exact div_pos (hT.2.2.2.1 j ω) (bOne_pos hT j ω)

/-- Cochrane (2023), §7.5, pp. 227–228 (Theorem P): **the policy satisfies every flow condition**
(7.1). -/
theorem polOne_flow (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    RealFlow 𝔼 β (polOneD 𝔼 D0 s e) (polOneX 𝔼 s e) s t := by
  intro ω
  rcases t with _ | t
  · -- date 0
    have hterm : ∀ j, β ^ (j + 1) * (sales (polOneD 𝔼 D0 s e) 0 (0 + (j + 1)) ω *
        𝔼.E 0 (polOneX 𝔼 s e (0 + (j + 1))) ω) =
        β ^ (j + 1) * 𝔼.E 0 (s (j + 1)) ω - β ^ (j + 1) * (D0 (j + 1) ω * e (j + 1) ω) := by
      intro j
      have hD1 : ∀ m, polOneD 𝔼 D0 s e 1 m = bOne 𝔼 s e m := fun m => by simp [polOneD]
      have hD0' : ∀ m, polOneD 𝔼 D0 s e 0 m = D0 m := fun m => by simp [polOneD]
      rw [zero_add, polOne_achieves hpo hdc hT]
      simp only [sales, zero_add, hD1, hD0', Pi.sub_apply, bOne, Pi.div_apply]
      have := hT.2.2.1 (j + 1) ω
      field_simp
    simp only [hterm]
    have h1 := (hasSum_nat_add_iff' 1).mpr (hT.2.2.2.2.2 ω)
    have h2 := (hasSum_nat_add_iff' 1).mpr
      (summable_surplusTerm 𝔼 hβ0 hβ1 hsb 0 ω).hasSum
    simp only [Finset.sum_range_one, pow_zero, one_mul] at h1 h2
    have h3 := h2.sub h1
    convert h3 using 1
    · funext j; simp [surplusTerm]
    · simp only [polOneD, polOneX, ↓reduceIte, surplusTerm, pow_zero, one_mul, hs 0, pvSurplus]
      ring
  · -- dates after 0: no trading
    have hz : (fun j : ℕ => β ^ (j + 1) * (sales (polOneD 𝔼 D0 s e) (t + 1) (t + 1 + (j + 1)) ω *
        𝔼.E (t + 1) (polOneX 𝔼 s e (t + 1 + (j + 1))) ω)) = fun _ => 0 := by
      funext j
      simp [sales, polOneD]
    rw [hz]
    convert hasSum_zero using 1
    simp only [polOneD, polOneX, Nat.add_one_ne_zero, ↓reduceIte, Pi.div_apply]
    have := bOne_pos hT t ω
    field_simp
    ring

/-- Cochrane (2023), §7.5, pp. 227–228 (Theorem P): **the policy satisfies every present-value
relation** (7.5), with (7.18) at date 0. -/
theorem polOne_presentValue (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M)
    (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    PresentValue 𝔼 β (polOneD 𝔼 D0 s e) (polOneX 𝔼 s e) s t := by
  intro ω
  refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
  rcases t with _ | t
  · convert hT.2.2.2.2.2 ω using 1
    funext j
    simp only [debtTerm, zero_add, polOneD, ↓reduceIte, polOne_achieves hpo hdc hT]
  · have heq : (fun j => debtTerm 𝔼 β (polOneD 𝔼 D0 s e) (polOneX 𝔼 s e) (t + 1) j ω) =
        fun j => surplusTerm 𝔼 β s (t + 1) j ω := by
      funext j
      simp only [debtTerm, surplusTerm, polOneD, Nat.add_one_ne_zero, ↓reduceIte]
      rw [show t + 1 + j = t + j + 1 by omega, polOne_E hpo hdc hT, Pi.div_apply]
      have := bOne_pos hT (t + j) ω
      field_simp
    rw [heq]
    exact (summable_surplusTerm 𝔼 hβ0 hβ1 hsb _ ω).hasSum

/-! ### The second policy (7.20): roll over one-period debt -/

/-- Cochrane (2023), eq. (7.20), p. 227: the present value of bounded surpluses is known at its
date. -/
theorem pvSurplus_adapted {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ M) (t : ℕ) : 𝔼.E t (pvSurplus 𝔼 β s t) = pvSurplus 𝔼 β s t := by
  funext ω
  have hb : ∀ k ω', |surplusTerm 𝔼 β s t k ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hsb _) _ ω') (pow_nonneg hβ0 k)
  change 𝔼.E t (fun ω' => ∑' k, surplusTerm 𝔼 β s t k ω') ω = _
  rw [𝔼.E_tsum hβ0 hβ1 hb t ω]
  refine tsum_congr fun k => ?_
  have : surplusTerm 𝔼 β s t k = β ^ k • 𝔼.E t (s (t + k)) := by
    funext ω'; simp [surplusTerm]
  rw [this, map_smul, 𝔼.E_E_self]

/-- Cochrane (2023), eq. (7.20), p. 227: with positive surpluses (positive date-0 expectations)
the date-0 expected present value is positive. -/
theorem E_pvSurplus_pos {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (j : ℕ) (ω : Ω)
    (hE : 0 < 𝔼.E 0 (s j) ω) : 0 < 𝔼.E 0 (pvSurplus 𝔼 β s j) ω := by
  have hb : ∀ k ω', |surplusTerm 𝔼 β s j k ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hsb _) _ ω') (pow_nonneg hβ0 k)
  change 0 < 𝔼.E 0 (fun ω' => ∑' k, surplusTerm 𝔼 β s j k ω') ω
  rw [𝔼.E_tsum hβ0 hβ1 hb 0 ω]
  have hterm : ∀ k, 𝔼.E 0 (surplusTerm 𝔼 β s j k) ω = β ^ k * 𝔼.E 0 (s (j + k)) ω := by
    intro k
    have : surplusTerm 𝔼 β s j k = β ^ k • 𝔼.E j (s (j + k)) := by
      funext ω'; simp [surplusTerm]
    rw [this, map_smul, 𝔼.tower (Nat.zero_le j)]
    rfl
  simp only [hterm]
  have hnn : ∀ k, 0 ≤ β ^ k * 𝔼.E 0 (s (j + k)) ω := fun k => by
    refine mul_nonneg (pow_nonneg hβ0 k) ?_
    have := 𝔼.mono 0 (show (fun _ => (0 : ℝ)) ≤ s (j + k) from fun ω' => hs0 _ ω') ω
    rwa [𝔼.const] at this
  have hsumm : Summable (fun k => β ^ k * 𝔼.E 0 (s (j + k)) ω) :=
    Summable.of_nonneg_of_le hnn (fun k => mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (𝔼.abs_E_le (hsb _) 0 ω)) (pow_nonneg hβ0 k))
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
  refine lt_of_lt_of_le ?_ (hsumm.le_tsum 0 fun k _ => hnn k)
  simpa using hE

/-- Cochrane (2023), eq. (7.20), p. 227: the second policy achieves the same targets,
`E_0(1/P_j) = e_j`, with positive price levels. -/
theorem polTwo_achieves (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (j : ℕ) :
    𝔼.E 0 (polTwoX 𝔼 β s e j) = e j ∧ ∀ ω, 0 < polTwoX 𝔼 β s e j ω := by
  rcases j with _ | j
  · simp only [polTwoX, ↓reduceIte]; exact ⟨hT.2.1 0, hT.2.2.1 0⟩
  · have hc : 𝔼.E 0 (cTwo 𝔼 β s e (j + 1)) = cTwo 𝔼 β s e (j + 1) :=
      hdc 0 _ _ (𝔼.E_E_self 0 _) (hT.2.1 _)
    have hEpos : ∀ ω, 0 < 𝔼.E 0 (pvSurplus 𝔼 β s (j + 1)) ω := fun ω =>
      E_pvSurplus_pos hβ0 hβ1 hsb hs0 (j + 1) ω (hT.2.2.2.2.1 j ω)
    simp only [polTwoX, Nat.add_one_ne_zero, ↓reduceIte]
    refine ⟨?_, fun ω => ?_⟩
    · rw [E_div_known 𝔼 hpo hdc hc]
      funext ω
      simp only [cTwo, Pi.div_apply]
      have := hEpos ω
      have := hT.2.2.1 (j + 1) ω
      field_simp
    · simp only [Pi.div_apply, cTwo]
      have hpv : 0 < pvSurplus 𝔼 β s (j + 1) ω := by
        have hnn : ∀ k, 0 ≤ surplusTerm 𝔼 β s (j + 1) k ω := fun k => by
          refine mul_nonneg (pow_nonneg hβ0 k) ?_
          have := 𝔼.mono (j + 1) (show (fun _ => (0 : ℝ)) ≤ s (j + 1 + k) from
            fun ω' => hs0 _ ω') ω
          rwa [𝔼.const] at this
        have hfirst : surplusTerm 𝔼 β s (j + 1) 0 ω = s (j + 1) ω := by
          simp [surplusTerm, hs (j + 1)]
        refine lt_of_lt_of_le ?_ ((summable_surplusTerm 𝔼 hβ0 hβ1 hsb _ ω).le_tsum 0
          fun k _ => hnn k)
        rw [hfirst]
        exact hT.2.2.2.1 j ω
      exact div_pos hpv (div_pos (hEpos ω) (hT.2.2.1 _ ω))

/-- Cochrane (2023), eq. (7.20), p. 227: the one-period debt of the second policy is positive and
known at every date. -/
theorem cTwo_pos_known (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω)
    (hT : Targets 𝔼 β D0 s e) (j t : ℕ) :
    (∀ ω, 0 < cTwo 𝔼 β s e (j + 1) ω) ∧ 𝔼.E t (cTwo 𝔼 β s e j) = cTwo 𝔼 β s e j := by
  refine ⟨fun ω => div_pos (E_pvSurplus_pos hβ0 hβ1 hsb hs0 (j + 1) ω (hT.2.2.2.2.1 j ω))
    (hT.2.2.1 _ ω), ?_⟩
  exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le t) (hdc 0 _ _ (𝔼.E_E_self 0 _) (hT.2.1 _))

/-- Cochrane (2023), eq. (7.20), p. 227: `B_{j−1}^{(j)} E_t(1/P_j) = E_t PV_j` for the second
policy. -/
theorem polTwo_E (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω)
    (hT : Targets 𝔼 β D0 s e) (t j : ℕ) (ω : Ω) :
    cTwo 𝔼 β s e (j + 1) ω * 𝔼.E t (polTwoX 𝔼 β s e (j + 1)) ω =
      𝔼.E t (pvSurplus 𝔼 β s (j + 1)) ω := by
  have hpos := (cTwo_pos_known hdc hβ0 hβ1 hsb hs0 hT j t).1
  have hk := (cTwo_pos_known hdc hβ0 hβ1 hsb hs0 hT (j + 1) t).2
  simp only [polTwoX, Nat.add_one_ne_zero, ↓reduceIte]
  rw [E_div_known 𝔼 hpo hdc hk, Pi.div_apply]
  have := hpos ω
  field_simp

/-- Cochrane (2023), eq. (7.20), p. 227: **the second policy satisfies every flow condition.** -/
theorem polTwo_flow (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    RealFlow 𝔼 β (polTwoD 𝔼 β D0 s e) (polTwoX 𝔼 β s e) s t := by
  intro ω
  have hrec := fun u => congrFun (pvSurplus_recursion 𝔼 hβ0 hβ1 hs hsb u) ω
  rcases t with _ | t
  · -- date 0: buy back long debt, issue one-period debt
    have hterm : ∀ j, β ^ (j + 1) * (sales (polTwoD 𝔼 β D0 s e) 0 (0 + (j + 1)) ω *
        𝔼.E 0 (polTwoX 𝔼 β s e (0 + (j + 1))) ω) =
        (Pi.single 0 (β * 𝔼.E 0 (pvSurplus 𝔼 β s 1) ω) : ℕ → ℝ) j -
          β ^ (j + 1) * (D0 (j + 1) ω * e (j + 1) ω) := by
      intro j
      rw [zero_add, (polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT (j + 1)).1]
      rcases j with _ | j
      · have h1 := polTwo_E hpo hdc hβ0 hβ1 hsb hs0 hT 0 0 ω
        rw [(polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT 1).1] at h1
        simp only [sales, polTwoD, zero_add, one_ne_zero, ↓reduceIte, Pi.sub_apply,
          Pi.single_eq_same, pow_one]
        rw [← h1]
        ring
      · simp only [sales, polTwoD, zero_add, one_ne_zero, ↓reduceIte, Pi.sub_apply,
          show j + 1 + 1 ≠ 1 by omega, Pi.single_eq_of_ne (show j + 1 ≠ 0 by omega)]
        simp
    simp only [hterm]
    have h1 := (hasSum_nat_add_iff' 1).mpr (hT.2.2.2.2.2 ω)
    simp only [Finset.sum_range_one, pow_zero, one_mul] at h1
    have h2 := (hasSum_pi_single 0 (β * 𝔼.E 0 (pvSurplus 𝔼 β s 1) ω)).sub h1
    convert h2 using 1
    have h0 := hrec 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add] at h0
    simp only [polTwoD, polTwoX, ↓reduceIte]
    linarith
  · -- later dates: one-period roll-over
    obtain ⟨hpos, -⟩ := cTwo_pos_known hdc hβ0 hβ1 hsb hs0 hT t 0
    have hterm : (fun j : ℕ => β ^ (j + 1) * (sales (polTwoD 𝔼 β D0 s e) (t + 1)
        (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (polTwoX 𝔼 β s e (t + 1 + (j + 1))) ω)) =
        Pi.single 0 (β * 𝔼.E (t + 1) (pvSurplus 𝔼 β s (t + 1 + 1)) ω) := by
      funext j
      rcases j with _ | j
      · have h1 := polTwo_E hpo hdc hβ0 hβ1 hsb hs0 hT (t + 1) (t + 1) ω
        simp only [sales, polTwoD, Nat.add_one_ne_zero, ↓reduceIte, Pi.sub_apply,
          show t + 1 + (0 + 1) ≠ t + 1 by omega, zero_add, Pi.zero_apply, sub_zero,
          Pi.single_eq_same, pow_one]
        rw [h1]
      · simp only [sales, polTwoD, Nat.add_one_ne_zero, ↓reduceIte,
          show t + 1 + (j + 1 + 1) ≠ t + 1 by omega, show t + 1 + (j + 1 + 1) ≠ t + 1 + 1 by omega,
          Pi.sub_apply, sub_self, Pi.zero_apply, zero_mul, mul_zero,
          Pi.single_eq_of_ne (show j + 1 ≠ 0 by omega)]
    rw [hterm]
    convert hasSum_pi_single 0 (β * 𝔼.E (t + 1) (pvSurplus 𝔼 β s (t + 1 + 1)) ω) using 1
    have h0 := hrec (t + 1)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
    simp only [polTwoD, polTwoX, Nat.add_one_ne_zero, ↓reduceIte, Pi.div_apply]
    have := hpos ω
    field_simp
    linarith

/-- Cochrane (2023), eq. (7.20), p. 227: **the second policy satisfies every present-value
relation.** -/
theorem polTwo_presentValue (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (t : ℕ) :
    PresentValue 𝔼 β (polTwoD 𝔼 β D0 s e) (polTwoX 𝔼 β s e) s t := by
  intro ω
  refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
  rcases t with _ | t
  · convert hT.2.2.2.2.2 ω using 1
    funext j
    simp only [debtTerm, zero_add, polTwoD, ↓reduceIte,
      (polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT j).1]
  · have heq : (fun j => debtTerm 𝔼 β (polTwoD 𝔼 β D0 s e) (polTwoX 𝔼 β s e) (t + 1) j ω) =
        Pi.single 0 (pvSurplus 𝔼 β s (t + 1) ω) := by
      funext j
      rcases j with _ | j
      · have h1 := polTwo_E hpo hdc hβ0 hβ1 hsb hs0 hT (t + 1) t ω
        rw [pvSurplus_adapted hβ0 hβ1 hsb] at h1
        simp only [debtTerm, polTwoD, Nat.add_one_ne_zero, ↓reduceIte, add_zero, pow_zero,
          one_mul, Pi.single_eq_same]
        exact h1
      · simp only [debtTerm, polTwoD, Nat.add_one_ne_zero, ↓reduceIte,
          show t + 1 + (j + 1) ≠ t + 1 by omega, Pi.zero_apply, zero_mul, mul_zero,
          Pi.single_eq_of_ne (show j + 1 ≠ 0 by omega)]
    rw [heq]
    exact hasSum_pi_single 0 _

/-- Cochrane (2023), §7.5, p. 227 (bullet, and p. 226): **many debt policies support the same
price-level path.** The two policies achieve the same `{E_0(1/P_j)}` and `P_0` but differ: the first
leaves `B_0^{(2)} > 0` outstanding, the second `B_0^{(2)} = 0`. -/
theorem policies_differ (hpo : 𝔼.PullOut) (hdc : DivClosed 𝔼) {β M : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {D0 : ℕ → Ω → ℝ} {s e : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hs0 : ∀ t ω, 0 ≤ s t ω) (hT : Targets 𝔼 β D0 s e) (ω : Ω) :
    (∀ j, 𝔼.E 0 (polOneX 𝔼 s e j) = 𝔼.E 0 (polTwoX 𝔼 β s e j)) ∧
      polOneD 𝔼 D0 s e 1 2 ω ≠ polTwoD 𝔼 β D0 s e 1 2 ω := by
  refine ⟨fun j => by rw [polOne_achieves hpo hdc hT,
    (polTwo_achieves hpo hdc hβ0 hβ1 hs hsb hs0 hT j).1], ?_⟩
  have h1 : polOneD 𝔼 D0 s e 1 2 ω = bOne 𝔼 s e 2 ω := by simp [polOneD]
  have h2 : polTwoD 𝔼 β D0 s e 1 2 ω = 0 := by simp [polTwoD]
  rw [h1, h2]
  exact (bOne_pos hT 1 ω).ne'

/-! ### Consequences of (7.18) -/

/-- Cochrane (2023), eq. (7.18), p. 227: conversely, every equilibrium satisfies (7.18), written
with nominal bond prices: `∑_j Q_0^{(j)} B_{−1}^{(j)} = P_0 E_0 ∑_j β^j s_j`. -/
theorem presentValue_zero_nominal (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hpv : PresentValue 𝔼 β D x s 0) (ω : Ω) :
    HasSum (fun j => bondPrice 𝔼 β P x 0 j ω * D 0 (0 + j) ω) (P 0 ω * pvSurplus 𝔼 β s 0 ω) :=
  nominalValue_eq 𝔼 hpo hP 0 ω (hpv ω).2

/-- Cochrane (2023), §7.5, p. 228: with only one-period debt outstanding at date 0
(`B_{−1}^{(j)} = 0` for `j ≥ 1`), `B_{−1}^{(0)}/P_0 = E_0 ∑ β^j s_j`: future price levels
(whatever debt policy sets them) do not affect `P_0`. -/
theorem onePeriod_price_zero {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hx : 𝔼.Adapted x) (hD : ∀ j, D 0 (j + 1) = 0) (hpv : PresentValue 𝔼 β D x s 0) (ω : Ω) :
    D 0 0 ω * x 0 ω = pvSurplus 𝔼 β s 0 ω := by
  have hs : HasSum (fun j => debtTerm 𝔼 β D x 0 j ω) (D 0 0 ω * x 0 ω) := by
    have : (fun j => debtTerm 𝔼 β D x 0 j ω) = Pi.single 0 (D 0 0 ω * x 0 ω) := by
      funext j
      rcases j with _ | j
      · simp [debtTerm, hx 0]
      · simp [debtTerm, hD j]
    rw [this]
    exact hasSum_pi_single 0 _
  exact hs.unique (hpv ω).2

/-- Cochrane (2023), §7.5, p. 228: **no free lunch for QE.** With nonnegative inherited positions
`B_{−1}^{(j)} ≥ 0` and the same surpluses, two price paths both consistent with (7.18), the second
with weakly higher expected price levels at every date with debt outstanding
(`E_0(1/P'_j) ≤ E_0(1/P_j)` when `B_{−1}^{(j)} > 0`), have the same expected price level at every
such date: a QE policy cannot raise near-term price levels without lowering some other. -/
theorem qe_tradeoff {β : ℝ} (hβ0 : 0 < β) {d e e' : ℕ → ℝ} {V : ℝ} (hd : ∀ j, 0 ≤ d j)
    (h : HasSum (fun j => β ^ j * (d j * e j)) V) (h' : HasSum (fun j => β ^ j * (d j * e' j)) V)
    (hle : ∀ j, 0 < d j → e' j ≤ e j) (j : ℕ) (hdj : 0 < d j) : e' j = e j := by
  have hdiff := h.sub h'
  rw [sub_self] at hdiff
  have hnn : ∀ i, 0 ≤ β ^ i * (d i * e i) - β ^ i * (d i * e' i) := fun i => by
    rw [← mul_sub, ← mul_sub]
    refine mul_nonneg (pow_nonneg hβ0.le i) ?_
    rcases (hd i).lt_or_eq with hdi | hdi
    · exact mul_nonneg (hd i) (sub_nonneg.mpr (hle i hdi))
    · rw [← hdi, zero_mul]
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hdiff) j
  simp only [Pi.zero_apply, ← mul_sub] at hz
  have := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero j hβ0.ne')
  have := (mul_eq_zero.mp this).resolve_left hdj.ne'
  linarith

/-- Cochrane (2023), §7.5, p. 228 (generalised "stepping on a rake"): with nonnegative inherited
positions, raising the expected price level at some date with debt outstanding requires lowering
it at some other date with debt outstanding. -/
theorem qe_tradeoff_strict {β : ℝ} (hβ0 : 0 < β) {d e e' : ℕ → ℝ} {V : ℝ}
    (hd : ∀ j, 0 ≤ d j) (h : HasSum (fun j => β ^ j * (d j * e j)) V)
    (h' : HasSum (fun j => β ^ j * (d j * e' j)) V) {j : ℕ} (hdj : 0 < d j) (hj : e' j < e j) :
    ∃ i, 0 < d i ∧ e i < e' i := by
  by_contra hcon
  push Not at hcon
  exact absurd (qe_tradeoff hβ0 hd h h' hcon j hdj) hj.ne

/-- Cochrane (2023), §7.5, p. 228 (E7.8): the nonnegativity of positions is needed. With
`B_{−1}^{(0)} = 1` and a negative position `B_{−1}^{(1)} = −1` (the government is long the
date-1 bond), lowering both `1/P_0` and `1/P_1` (raising both price levels) keeps (7.18). -/
theorem qe_negative_position {β δ x0 e1 : ℝ} (hβ0 : 0 < β) (hδ : 0 < δ) :
    let d : ℕ → ℝ := fun j => if j = 0 then 1 else if j = 1 then -1 else 0
    let e : ℕ → ℝ := fun j => if j = 0 then x0 else e1
    let e' : ℕ → ℝ := fun j => if j = 0 then x0 - δ else e1 - δ / β
    HasSum (fun j => β ^ j * (d j * e j)) (x0 - β * e1) ∧
      HasSum (fun j => β ^ j * (d j * e' j)) (x0 - β * e1) ∧ e' 0 < e 0 ∧ e' 1 < e 1 := by
  intro d e e'
  have hz : ∀ (f : ℕ → ℝ), ∀ j ∉ Finset.range 2, β ^ j * (d j * f j) = 0 := by
    intro f j hj
    simp only [Finset.mem_range, not_lt] at hj
    simp [d, show j ≠ 0 by omega, show j ≠ 1 by omega]
  have h1 : HasSum (fun j => β ^ j * (d j * e j)) (∑ j ∈ Finset.range 2, β ^ j * (d j * e j)) :=
    hasSum_sum_of_ne_finset_zero (hz e)
  have h2 : HasSum (fun j => β ^ j * (d j * e' j))
      (∑ j ∈ Finset.range 2, β ^ j * (d j * e' j)) := hasSum_sum_of_ne_finset_zero (hz e')
  have v1 : ∑ j ∈ Finset.range 2, β ^ j * (d j * e j) = x0 - β * e1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d, e]
    norm_num
    ring
  have v2 : ∑ j ∈ Finset.range 2, β ^ j * (d j * e' j) = x0 - β * e1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, d, e']
    norm_num
    field_simp
    ring
  rw [v1] at h1
  rw [v2] at h2
  refine ⟨h1, h2, ?_, ?_⟩
  · simp only [e, e', ↓reduceIte]; linarith
  · simp only [e, e', one_ne_zero, ↓reduceIte]
    have : 0 < δ / β := div_pos hδ hβ0
    linarith

/-- Cochrane (2023), §7.5, p. 228: **debt policy can offset a fiscal shock.** Suppose (7.18)
holds, `B_{−1}^{(0)} x_0 + ∑_{j≥1} β^j B_{−1}^{(j)} e_j = V`, and the present value of surpluses
falls to `V − Δ`. Lowering the target `e_{j₀}` of one maturity with `B_{−1}^{(j₀)} > 0` by
`Δ/(β^{j₀} B_{−1}^{(j₀)})` restores (7.18) with the same `1/P_0 = x_0`: no current inflation, at the
cost of a higher price level at `j₀`. -/
theorem offset_shock {β V R Δ x0 : ℝ} (hβ0 : 0 < β) {d e : ℕ → ℝ} (j₀ : ℕ)
    (hd : 0 < d (j₀ + 1))
    (hR : HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e (j + 1))) R) (h718 : d 0 * x0 + R = V) :
    let e' : ℕ → ℝ := fun j => if j = j₀ + 1 then e j - Δ / (β ^ j * d j) else e j
    HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e' (j + 1))) (R - Δ) ∧
      d 0 * x0 + (R - Δ) = V - Δ ∧ (0 < Δ → e' (j₀ + 1) < e (j₀ + 1)) := by
  intro e'
  have hp : 0 < β ^ (j₀ + 1) * d (j₀ + 1) := mul_pos (pow_pos hβ0 _) hd
  refine ⟨?_, by linarith, fun hΔ => ?_⟩
  · have hcorr : HasSum (fun j => if j = j₀ then Δ else 0) Δ := hasSum_ite_eq j₀ Δ
    convert hR.sub hcorr using 1
    funext j
    by_cases hj : j = j₀
    · subst hj
      simp only [e', ↓reduceIte]
      field_simp
    · simp only [e', hj, ↓reduceIte, show j + 1 ≠ j₀ + 1 by omega, sub_zero]
  · simp only [e', ↓reduceIte]
    have : 0 < Δ / (β ^ (j₀ + 1) * d (j₀ + 1)) := div_pos hΔ hp
    linarith

/-- Cochrane (2023), §7.5, p. 228: **debt policy cannot eliminate the inflation.** If the present
value falls (`V' < V`) and `1/P_0 = x_0` is held fixed, then with nonnegative positions some
date with debt outstanding has a lower `E_0(1/P_j)` (a higher expected price level). -/
theorem offset_shock_cost {β V V' R R' x0 : ℝ} (hβ0 : 0 < β) {d e e' : ℕ → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hR : HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e (j + 1))) R)
    (hR' : HasSum (fun j => β ^ (j + 1) * (d (j + 1) * e' (j + 1))) R')
    (h718 : d 0 * x0 + R = V) (h718' : d 0 * x0 + R' = V') (hVV : V' < V) :
    ∃ j, 0 < d (j + 1) ∧ e' (j + 1) < e (j + 1) := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ j, β ^ (j + 1) * (d (j + 1) * e (j + 1)) ≤
      β ^ (j + 1) * (d (j + 1) * e' (j + 1)) := by
    intro j
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le _)
    rcases (hd (j + 1)).lt_or_eq with h | h
    · exact mul_le_mul_of_nonneg_left (hcon j h) (hd _)
    · rw [← h, zero_mul, zero_mul]
  have := hasSum_le hle hR hR'
  linarith

/-- Cochrane (2023), eq. (7.21), p. 228: **the end-of-period value of debt.** In any equilibrium
(present value at date 1, dominated debt series), `∑_{j≥1} β^j B_0^{(j)} E_0(1/P_j) =
E_0 ∑_{j≥1} β^j s_j`, whatever the quantities `B_0^{(j)}` sold. -/
theorem end_of_period_value (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hdom : DebtDominated 𝔼 β D x 1)
    (hpv : PresentValue 𝔼 β D x s 1) (ω : Ω) :
    HasSum (fun j => β ^ (j + 1) * (D 1 (j + 1) ω * 𝔼.E 0 (x (j + 1)) ω))
      (pvSurplus 𝔼 β s 0 ω - s 0 ω) := by
  have h1 := (hasSum_E_debtValue_succ 𝔼 hpo hD (t := 0) hdom ω).mul_left β
  have hV : debtValue 𝔼 β D x 1 = pvSurplus 𝔼 β s 1 := by
    funext ω'; exact (hpv ω').2.tsum_eq
  have hrec := congrFun (pvSurplus_recursion 𝔼 hβ0 hβ1 hs hsb 0) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add] at hrec
  rw [hV] at h1
  convert h1 using 1
  · funext j
    rw [zero_add, add_comm 1 j, pow_succ]
    ring
  · linarith

/-- Cochrane (2023), eq. (7.21), p. 228, in nominal form: `∑_{j≥1} Q_0^{(j)} B_0^{(j)} / P_0 =
E_0 ∑_{j≥1} β^j s_j`. -/
theorem end_of_period_value_nominal (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {P x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hP : 𝔼.Adapted P)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hs : 𝔼.Adapted s)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hdom : DebtDominated 𝔼 β D x 1)
    (hpv : PresentValue 𝔼 β D x s 1) (ω : Ω) :
    HasSum (fun j => bondPrice 𝔼 β P x 0 (j + 1) ω * D 1 (j + 1) ω * x 0 ω)
      (pvSurplus 𝔼 β s 0 ω - s 0 ω) := by
  convert end_of_period_value hpo hβ0 hβ1 hD hs hsb hdom hpv ω using 1
  funext j
  rw [bondPrice_eq 𝔼 hpo hP]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, zero_add]
  linear_combination (β ^ (j + 1) * D 1 (j + 1) ω * 𝔼.E 0 (x (j + 1)) ω) * hPx 0 ω

end Cochrane.LongTermDebtDynamics.PolicyConstraints
