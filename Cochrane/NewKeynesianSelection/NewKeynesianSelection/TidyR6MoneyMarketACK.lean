/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.SelectionPatches

/-!
# A money market in the Atkeson–Chari–Kehoe regime

Cochrane (2023), Chapter 16, §16.10.2, p. 389: Atkeson, Chari and Kehoe (2010) "model an economy
with constant velocity and hence money demand `M_tV = P_ty`. The central bank operates by setting
the money supply in both interest-rate target and money-growth regimes." "How could a central
bank, with one instrument, the money supply `{M_T, M_{T+1}}`, simultaneously set `i_T` to a large
level and `π_{T+1}` to a low level?" "Velocity is interest-elastic. With interest-elastic money
demand, a constant money growth rule leaves just as many indeterminacies as the interest-rate
rule … It doesn't even stop inflation, let alone rule out the equilibrium path."

The perfect-foresight model of `SelectionPatches.ACKEq` is given an explicit money market:
nominal money `M_t`, price level `P_t`, money demand `M_t = P_t y L(i_t)`, the Fisher equation
`1 + i_t = (1 + r)Π_{t+1}` and the money-growth rule `M_{t+1} = μM_t` imposed on money itself
(`ACKMoney`, `MoneyRuleEq`).

## Main results

* `money_growth`: money demand in growth form, `M_{t+1}/M_t = Π_{t+1}L(i_{t+1})/L(i_t)`.
* Constant velocity (`L` constant): `cv_money_sets_rate` (one instrument: the money path fixes
  both `Π_{t+1} = M_{t+1}/M_t` and `1 + i_t = (1 + r)M_{t+1}/M_t`), `cv_ackEq` (the money-market
  model is `SelectionPatches.ACKEq`), `cv_overlap` (at the first exceedance `Φ(Π_T) = μ`),
  `cv_ack_pruned` (no equilibrium ever exceeds `Π_U`), `cv_moneyRule` (a money-growth rule pins
  `Π_{t+1} = μ`).
* Interest-elastic (Cagan) demand `L(i) = e^{−αi}`: `cagan_step`, `caganNext` (the forced next
  rate), `cagan_moneyRule_continuum` (under a money-growth rule, every initial rate
  `i_0 ≥ (1 + r)μ − 1` starts an equilibrium respecting the zero bound, with
  `Π_1 = (1 + i_0)/(1 + r)`, so a continuum of equilibria and inflation not pinned at `μ`),
  `cagan_ack_not_pruned` (every Taylor path whose first exceedance of `Π_U` has `Φ(Π_T) > μ`
  continues as an ACK equilibrium: the overlap period is consistent, the inflation is neither
  ruled out nor stopped), and `ack_needs_constant_velocity` (the contrast in one statement).
-/

namespace Cochrane.NewKeynesianSelection.TidyR6MoneyMarketACK

open Filter Topology

/-! ## The money market -/

/-- Cochrane (2023), §16.10.2, p. 389: a perfect-foresight equilibrium of the ACK regime with an
explicit money market. Positive prices with `P_{t+1} = Π_{t+1}P_t`, positive inflation, the zero
bound, the Fisher equation (16.28), money demand `M_t = P_t y L(i_t)`, the Taylor rule (16.27)
up to and including the first period with `Π_T > Π_U`, and the money-growth rule
`M_{t+1} = μM_t` from that period on. -/
def ACKMoney (r y μ PiU : ℝ) (L Φ : ℝ → ℝ) (P M infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < P t) ∧ (∀ t, P (t + 1) = infl (t + 1) * P t) ∧ (∀ t, 0 < infl t) ∧
    (∀ t, 0 ≤ i t) ∧ (∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ∧
    (∀ t, M t = P t * y * L (i t)) ∧
    (∀ t, (∀ s < t, infl s ≤ PiU) → 1 + i t = (1 + r) * Φ (infl t)) ∧
    ∀ t, (∃ s ≤ t, PiU < infl s) → M (t + 1) = μ * M t

/-- Cochrane (2023), §16.10.2, p. 389 and §19.2: a perfect-foresight equilibrium under a
money-growth rule `M_{t+1} = μM_t` at every date, with money demand `M_t = P_t y L(i_t)`. -/
def MoneyRuleEq (r y μ : ℝ) (L : ℝ → ℝ) (P M infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < P t) ∧ (∀ t, P (t + 1) = infl (t + 1) * P t) ∧ (∀ t, 0 < infl t) ∧
    (∀ t, 0 ≤ i t) ∧ (∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) ∧
    (∀ t, M t = P t * y * L (i t)) ∧ ∀ t, M (t + 1) = μ * M t

/-- Cochrane (2023), §16.10.2, p. 389: with money demand `M_t = P_t y L(i_t)` and
`P_{t+1} = Π_{t+1}P_t`, money grows at `M_{t+1}/M_t = Π_{t+1}L(i_{t+1})/L(i_t)`. -/
theorem money_growth {y : ℝ} {L : ℝ → ℝ} {P M infl i : ℕ → ℝ} (hy : y ≠ 0)
    (hP : ∀ t, 0 < P t) (hPs : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hM : ∀ t, M t = P t * y * L (i t)) (t : ℕ) (hL : L (i t) ≠ 0) :
    M (t + 1) / M t = infl (t + 1) * (L (i (t + 1)) / L (i t)) := by
  rw [hM, hM, hPs]
  have := (hP t).ne'
  field_simp

/-! ## Constant velocity -/

/-- Cochrane (2023), §16.10.2, p. 389, "with one instrument, the money supply `{M_T, M_{T+1}}`":
with constant velocity (`L ≡ ℓ > 0`, `y > 0`) the money path alone fixes inflation,
`Π_{t+1} = M_{t+1}/M_t`, and through the Fisher equation the nominal rate,
`1 + i_t = (1 + r)M_{t+1}/M_t`; the bank cannot set the two separately. -/
theorem cv_money_sets_rate {r y ℓ : ℝ} {P M infl i : ℕ → ℝ} (hy : 0 < y) (hℓ : 0 < ℓ)
    (hr : 0 < 1 + r) (hP : ∀ t, 0 < P t) (hPs : ∀ t, P (t + 1) = infl (t + 1) * P t)
    (hM : ∀ t, M t = P t * y * (fun _ => ℓ) (i t))
    (hfis : ∀ t, infl (t + 1) = (1 + r)⁻¹ * (1 + i t)) (t : ℕ) :
    infl (t + 1) = M (t + 1) / M t ∧ 1 + i t = (1 + r) * (M (t + 1) / M t) := by
  have h := money_growth (L := fun _ => ℓ) (i := i) hy.ne' hP hPs hM t hℓ.ne'
  simp only [div_self hℓ.ne', mul_one] at h
  refine ⟨h.symm, ?_⟩
  rw [h, hfis t, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- Cochrane (2023), §16.10.2, p. 389: with constant velocity the money-market ACK model is the
inflation model `SelectionPatches.ACKEq`: the money rule `M_{t+1} = μM_t` is `Π_{t+1} = μ`. -/
theorem cv_ackEq {r y ℓ μ PiU : ℝ} {Φ : ℝ → ℝ} {P M infl i : ℕ → ℝ} (hy : 0 < y)
    (hℓ : 0 < ℓ) (h : ACKMoney r y μ PiU (fun _ => ℓ) Φ P M infl i) :
    SelectionPatches.ACKEq r Φ PiU μ infl i := by
  obtain ⟨hP, hPs, hpos, hi, hfis, hM, htay, hmon⟩ := h
  refine ⟨hpos, hi, hfis, htay, fun t ht => ?_⟩
  have h1 := hmon t ht
  rw [hM, hM, hPs] at h1
  have hPt := hP t
  have : infl (t + 1) * (P t * y * ℓ) = μ * (P t * y * ℓ) := by linarith
  exact mul_right_cancel₀ (by positivity) this

/-- Cochrane (2023), §16.10.2, p. 389, "an equilibrium cannot form at period `T`", in the money
market: with constant velocity, at the first period with `Π_T > Π_U` an equilibrium needs
`Φ(Π_T) = μ`. -/
theorem cv_overlap {r y ℓ μ PiU : ℝ} {Φ : ℝ → ℝ} {P M infl i : ℕ → ℝ} (hy : 0 < y)
    (hℓ : 0 < ℓ) (hr : 0 < 1 + r) (h : ACKMoney r y μ PiU (fun _ => ℓ) Φ P M infl i) {T : ℕ}
    (hT : PiU < infl T) (hbefore : ∀ s < T, infl s ≤ PiU) : Φ (infl T) = μ :=
  SelectionPatches.ack_inconsistent hr (cv_ackEq hy hℓ h) hT hbefore

/-- Cochrane (2023), §16.10.2, p. 389, "the inflationary path leading to `T` is not an
equilibrium": with constant velocity and `Φ(Π) ≠ μ` above `Π_U`, no equilibrium of the
money-market ACK model ever exceeds `Π_U`. -/
theorem cv_ack_pruned {r y ℓ μ PiU : ℝ} {Φ : ℝ → ℝ} {P M infl i : ℕ → ℝ} (hy : 0 < y)
    (hℓ : 0 < ℓ) (hr : 0 < 1 + r) (hΦμ : ∀ x, PiU < x → Φ x ≠ μ)
    (h : ACKMoney r y μ PiU (fun _ => ℓ) Φ P M infl i) : ∀ t, infl t ≤ PiU :=
  SelectionPatches.ack_bounded hr hΦμ (cv_ackEq hy hℓ h)

/-- Cochrane (2023), §16.10.2, p. 389: with constant velocity a money-growth rule pins inflation,
`Π_{t+1} = μ` at every date. -/
theorem cv_moneyRule {r y ℓ μ : ℝ} {P M infl i : ℕ → ℝ} (hy : 0 < y) (hℓ : 0 < ℓ)
    (h : MoneyRuleEq r y μ (fun _ => ℓ) P M infl i) (t : ℕ) : infl (t + 1) = μ := by
  obtain ⟨hP, hPs, -, -, -, hM, hmon⟩ := h
  have h1 := hmon t
  rw [hM, hM, hPs] at h1
  have hPt := hP t
  have : infl (t + 1) * (P t * y * ℓ) = μ * (P t * y * ℓ) := by linarith
  exact mul_right_cancel₀ (by positivity) this

/-! ## Interest-elastic (Cagan) money demand -/

/-- Cochrane (2023), §16.10.2, p. 389 ("velocity is interest-elastic"): Cagan money demand
`L(i) = e^{−αi}`. -/
noncomputable def cagan (α : ℝ) (i : ℝ) : ℝ := Real.exp (-(α * i))

/-- Cochrane (2023), §16.10.2, p. 389: under a money-growth rule with Cagan demand, the money
market at `t + 1` forces the rate `i_{t+1} = i_t + α⁻¹ log((1 + i_t)/((1 + r)μ))`. -/
noncomputable def caganNext (r α μ : ℝ) (i : ℝ) : ℝ :=
  i + α⁻¹ * Real.log ((1 + i) / ((1 + r) * μ))

/-- Cochrane (2023), §16.10.2, p. 389: the forced rate clears the money market:
`Π_{t+1}L(i_{t+1}) = μL(i_t)` with `Π_{t+1} = (1 + i_t)/(1 + r)`. -/
theorem cagan_step {r α μ i : ℝ} (hα : 0 < α) (hr : 0 < 1 + r) (hμ : 0 < μ) (hi : 0 < 1 + i) :
    (1 + r)⁻¹ * (1 + i) * cagan α (caganNext r α μ i) = μ * cagan α i := by
  unfold cagan caganNext
  have hq : 0 < (1 + i) / ((1 + r) * μ) := by positivity
  have e : -(α * (i + α⁻¹ * Real.log ((1 + i) / ((1 + r) * μ)))) =
      -(α * i) + -Real.log ((1 + i) / ((1 + r) * μ)) := by
    field_simp
    ring
  rw [e, Real.exp_add, Real.exp_neg (Real.log ((1 + i) / ((1 + r) * μ))), Real.exp_log hq]
  field_simp

/-- Cochrane (2023), §16.10.2, p. 389: at or above `i* = (1 + r)μ − 1` the forced rate does not
fall, `i_{t+1} ≥ i_t`. -/
theorem caganNext_ge {r α μ i : ℝ} (hα : 0 < α) (hr : 0 < 1 + r) (hμ : 0 < μ)
    (hi : (1 + r) * μ - 1 ≤ i) : i ≤ caganNext r α μ i := by
  unfold caganNext
  have hpos : 0 < (1 + r) * μ := by positivity
  have h1 : 1 ≤ (1 + i) / ((1 + r) * μ) := by rw [le_div_iff₀ hpos]; linarith
  have := Real.log_nonneg h1
  have := inv_pos.mpr hα
  nlinarith

/-- Cochrane (2023), §16.10.2, p. 389: iterates of the forced rate from `i ≥ i*` stay at or
above `i`. -/
theorem caganNext_iterate_ge {r α μ i : ℝ} (hα : 0 < α) (hr : 0 < 1 + r) (hμ : 0 < μ)
    (hi : (1 + r) * μ - 1 ≤ i) (k : ℕ) : i ≤ (caganNext r α μ)^[k] i := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (caganNext_ge hα hr hμ (hi.trans ih))

/-- Cochrane (2023), p. 389: the price level built from `P_0` and an inflation path,
`P_t = P_0 ∏_{k<t} Π_{k+1}`. -/
noncomputable def priceFrom (P0 : ℝ) (infl : ℕ → ℝ) (t : ℕ) : ℝ :=
  P0 * ∏ k ∈ Finset.range t, infl (k + 1)

/-- Cochrane (2023), p. 389: `P_{t+1} = Π_{t+1}P_t` for `priceFrom`. -/
theorem priceFrom_succ (P0 : ℝ) (infl : ℕ → ℝ) (t : ℕ) :
    priceFrom P0 infl (t + 1) = infl (t + 1) * priceFrom P0 infl t := by
  unfold priceFrom
  rw [Finset.prod_range_succ]
  ring

/-- Cochrane (2023), p. 389: `priceFrom` is positive for positive `P_0` and inflation. -/
theorem priceFrom_pos {P0 : ℝ} {infl : ℕ → ℝ} (hP0 : 0 < P0) (hπ : ∀ t, 0 < infl t) (t : ℕ) :
    0 < priceFrom P0 infl t :=
  mul_pos hP0 (Finset.prod_pos fun k _ => hπ (k + 1))

/-- Cochrane (2023), §16.10.2, p. 389, "with interest-elastic money demand, a constant money
growth rule leaves just as many indeterminacies as the interest-rate rule": with Cagan demand
(`α > 0`), `μ > 0`, `1 + r > 0`, `(1 + r)μ ≥ 1`, every initial rate
`i_0 ≥ (1 + r)μ − 1`, every `Π_0 > 0` and `P_0 > 0` start an equilibrium of the money-growth
rule respecting the zero bound, with `Π_1 = (1 + i_0)/(1 + r)`. Distinct `i_0` give distinct
inflation, and for `i_0 > (1 + r)μ − 1` inflation is not `μ`: the rule neither determines nor
stops inflation. -/
theorem cagan_moneyRule_continuum {r y α μ : ℝ} (hα : 0 < α) (hμ : 0 < μ)
    (hr : 0 < 1 + r) (hrμ : 1 ≤ (1 + r) * μ) {i0 Pi0 P0 : ℝ} (hi0 : (1 + r) * μ - 1 ≤ i0)
    (hPi0 : 0 < Pi0) (hP0 : 0 < P0) :
    ∃ P M infl i : ℕ → ℝ, MoneyRuleEq r y μ (cagan α) P M infl i ∧ i 0 = i0 ∧
      infl 1 = (1 + r)⁻¹ * (1 + i0) ∧ ((1 + r) * μ - 1 < i0 → infl 1 ≠ μ) := by
  set i : ℕ → ℝ := fun t => (caganNext r α μ)^[t] i0 with hidef
  have hige : ∀ t, i0 ≤ i t := fun t => caganNext_iterate_ge hα hr hμ hi0 t
  have hi : ∀ t, 0 ≤ i t := fun t => by linarith [hige t]
  set infl : ℕ → ℝ := fun t => Nat.casesOn t Pi0 fun s => (1 + r)⁻¹ * (1 + i s) with hπdef
  have hπ : ∀ t, 0 < infl t := by
    intro t
    cases t with
    | zero => exact hPi0
    | succ s => exact mul_pos (inv_pos.mpr hr) (by linarith [hi s])
  set M : ℕ → ℝ := fun t => priceFrom P0 infl t * y * cagan α (i t) with hMdef
  refine ⟨priceFrom P0 infl, M, infl, i, ⟨priceFrom_pos hP0 hπ, priceFrom_succ P0 infl, hπ, hi,
    fun t => rfl,
    fun t => rfl, fun t => ?_⟩, rfl, rfl, fun hlt he => ?_⟩
  · simp only [hMdef]
    rw [priceFrom_succ]
    have hnext : i (t + 1) = caganNext r α μ (i t) := by
      simp only [hidef]; rw [Function.iterate_succ_apply']
    have hs := cagan_step hα hr hμ (i := i t) (by linarith [hi t])
    rw [hnext]
    change (1 + r)⁻¹ * (1 + i t) * priceFrom P0 infl t * y * cagan α (caganNext r α μ (i t)) = _
    calc (1 + r)⁻¹ * (1 + i t) * priceFrom P0 infl t * y * cagan α (caganNext r α μ (i t))
        = ((1 + r)⁻¹ * (1 + i t) * cagan α (caganNext r α μ (i t))) *
            (priceFrom P0 infl t * y) := by ring
      _ = μ * (priceFrom P0 infl t * y * cagan α (i t)) := by rw [hs]; ring
  · have : (1 + r)⁻¹ * (1 + i0) = μ := he
    rw [inv_mul_eq_iff_eq_mul₀ hr.ne'] at this
    linarith

/-- Cochrane (2023), §16.10.2, p. 389, with interest-elastic money demand the ACK regime does not
rule out the inflationary path, nor stop it. Let `Φ ≥ β` on `(0, ∞)` and let the Taylor orbit
`Φ^[t](Π₀)` first exceed `Π_U` at `T` with `Φ(Π_T) > μ` (a high rate at `T`, the case the
regime is designed for). With Cagan demand there is an equilibrium of the money-market ACK model
following the Taylor orbit up to `T` (so `Π_T > Π_U`), with the overlap period `T` consistent
and money growing at `μ` from `T` on. -/
theorem cagan_ack_not_pruned {r y α μ PiU Pi0 P0 : ℝ} {Φ : ℝ → ℝ} (hα : 0 < α) (hμ : 0 < μ)
    (hr : 0 < 1 + r) (hPi0 : 0 < Pi0) (hP0 : 0 < P0)
    (hbd : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) {T : ℕ} (hT : PiU < Φ^[T] Pi0)
    (hbefore : ∀ s < T, Φ^[s] Pi0 ≤ PiU) (hgt : μ < Φ (Φ^[T] Pi0)) :
    ∃ P M infl i : ℕ → ℝ, ACKMoney r y μ PiU (cagan α) Φ P M infl i ∧
      (∀ t ≤ T, infl t = Φ^[t] Pi0) ∧ PiU < infl T := by
  have horb : ∀ t, 0 < Φ^[t] Pi0 := by
    intro t
    induction t with
    | zero => simpa using hPi0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact lt_of_lt_of_le (inv_pos.mpr hr) (hbd _ ih)
  set iT : ℝ := (1 + r) * Φ (Φ^[T] Pi0) - 1 with hiT
  have hiT_ge : (1 + r) * μ - 1 ≤ iT := by
    have := mul_lt_mul_of_pos_left hgt hr
    linarith
  have hTay0 : ∀ t, 0 ≤ (1 + r) * Φ (Φ^[t] Pi0) - 1 := by
    intro t
    have h1 := mul_le_mul_of_nonneg_left (hbd _ (horb t)) hr.le
    rw [mul_inv_cancel₀ hr.ne'] at h1
    linarith
  set i : ℕ → ℝ := fun t => if t ≤ T then (1 + r) * Φ (Φ^[t] Pi0) - 1
    else (caganNext r α μ)^[t - T] iT with hidef
  have hi : ∀ t, 0 ≤ i t := by
    intro t
    simp only [hidef]
    split_ifs with h
    · exact hTay0 t
    · have := caganNext_iterate_ge hα hr hμ hiT_ge (t - T)
      linarith [hTay0 T]
  -- for `t ≥ T` the rate is the iterate of the forced rate from `i_T`
  have hiter : ∀ t, T ≤ t → i t = (caganNext r α μ)^[t - T] iT := by
    intro t ht
    simp only [hidef]
    split_ifs with h
    · have : t = T := le_antisymm h ht
      subst this
      simp [hiT]
    · rfl
  set infl : ℕ → ℝ := fun t => Nat.casesOn t Pi0 fun s => (1 + r)⁻¹ * (1 + i s) with hπdef
  have hπ : ∀ t, 0 < infl t := by
    intro t
    cases t with
    | zero => exact hPi0
    | succ s => exact mul_pos (inv_pos.mpr hr) (by linarith [hi s])
  have horbit : ∀ t ≤ T, infl t = Φ^[t] Pi0 := by
    intro t ht
    induction t with
    | zero => rfl
    | succ n _ =>
      change (1 + r)⁻¹ * (1 + i n) = _
      have hn : n ≤ T := by omega
      simp only [hidef, hn, ↓reduceIte]
      rw [Function.iterate_succ_apply']
      field_simp
      ring
  set M : ℕ → ℝ := fun t => priceFrom P0 infl t * y * cagan α (i t) with hMdef
  refine ⟨priceFrom P0 infl, M, infl, i, ⟨priceFrom_pos hP0 hπ, priceFrom_succ P0 infl, hπ, hi,
    fun t => rfl,
    fun t => rfl, fun t ht => ?_, fun t ht => ?_⟩, horbit, by rw [horbit T le_rfl]; exact hT⟩
  · -- the Taylor rule holds up to and including `T`
    have htT : t ≤ T := by
      by_contra hc
      push Not at hc
      have := ht T hc
      rw [horbit T le_rfl] at this
      linarith
    simp only [hidef, htT, ↓reduceIte, horbit t htT]
    ring
  · -- the money rule holds from `T` on
    obtain ⟨s, hs, hsU⟩ := ht
    have htT : T ≤ t := by
      by_contra hc
      push Not at hc
      have := hbefore s (lt_of_le_of_lt hs hc)
      rw [horbit s (by omega)] at hsU
      linarith
    simp only [hMdef]
    rw [priceFrom_succ]
    have hnext : i (t + 1) = caganNext r α μ (i t) := by
      rw [hiter (t + 1) (by omega), hiter t htT, show t + 1 - T = (t - T) + 1 by omega,
        Function.iterate_succ_apply']
    have hs' := cagan_step hα hr hμ (i := i t) (by linarith [hi t])
    rw [hnext]
    change (1 + r)⁻¹ * (1 + i t) * priceFrom P0 infl t * y * cagan α (caganNext r α μ (i t)) = _
    calc (1 + r)⁻¹ * (1 + i t) * priceFrom P0 infl t * y * cagan α (caganNext r α μ (i t))
        = ((1 + r)⁻¹ * (1 + i t) * cagan α (caganNext r α μ (i t))) *
            (priceFrom P0 infl t * y) := by ring
      _ = μ * (priceFrom P0 infl t * y * cagan α (i t)) := by rw [hs']; ring

/-- Cochrane (2023), §16.10.2, p. 389, the contrast in one statement: for the same rule `Φ`
(`Φ ≥ β`, `Φ(Π) > μ` above `Π_U`) and a Taylor orbit that first exceeds `Π_U` at `T`, constant
velocity rules out every path above `Π_U`, while Cagan demand admits the orbit up to `T` as an
equilibrium. The ACK "blow-up" depends on constant velocity. -/
theorem ack_needs_constant_velocity {r y ℓ α μ PiU Pi0 P0 : ℝ} {Φ : ℝ → ℝ} (hα : 0 < α)
    (hy : 0 < y) (hℓ : 0 < ℓ) (hμ : 0 < μ) (hr : 0 < 1 + r) (hPi0 : 0 < Pi0) (hP0 : 0 < P0)
    (hbd : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) (habove : ∀ x, PiU < x → μ < Φ x) {T : ℕ}
    (hT : PiU < Φ^[T] Pi0) (hbefore : ∀ s < T, Φ^[s] Pi0 ≤ PiU) :
    (∀ P M infl i, ACKMoney r y μ PiU (fun _ => ℓ) Φ P M infl i → ∀ t, infl t ≤ PiU) ∧
      ∃ P M infl i : ℕ → ℝ, ACKMoney r y μ PiU (cagan α) Φ P M infl i ∧ PiU < infl T :=
  by
  refine ⟨fun _ _ _ _ h => cv_ack_pruned hy hℓ hr (fun x hx => (habove x hx).ne') h, ?_⟩
  obtain ⟨P, M, infl, i, h, -, hT'⟩ :=
    cagan_ack_not_pruned (y := y) hα hμ hr hPi0 hP0 hbd hT hbefore (habove _ hT)
  exact ⟨P, M, infl, i, h, hT'⟩

end Cochrane.NewKeynesianSelection.TidyR6MoneyMarketACK
