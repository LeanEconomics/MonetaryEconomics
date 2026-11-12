/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.SpreadTarget

/-!
# The IS shock enters output through unexpected inflation (E9.7)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.4.1,
eqs. (9.22) and (9.24)–(9.26), pp. 275–278 (survey error E9.7).

The book says that with a spread target "the IS shock does not appear in equilibrium output".
`SpreadTarget.x_formula` proves this **given inflation**: `κ x_t = (1 − β)π^{e*} + ΔE_t π_t −
u_{π,t}`. But unexpected inflation is set by the valuation equation (9.22), whose discount-rate
terms are real rates, and by (9.26) the real rate loads on `u_x`. Hence `u_x` enters output through
`ΔE_t π_t`.

## Main results

* `innov_pi_later`: with the spread target, `ΔE_{t+1} π_{t+2+j} = 0` for `j ≥ 0`.
* `sigma_innov_i`: the news in the nominal rate,
  `σ ΔE_{t+1} i_s = (−ΔE_{t+1} π_s + ΔE_{t+1}(u_{π,s} − E_s u_{π,s+1}))/κ + ΔE_{t+1} u_{x,s}`.
* `discount_terms`: the discount-rate terms of (9.22) equal
  `(−(ρ/κ) ΔE π_{t+1} + U + W/κ)/σ` with `U = ∑ ρ^{j+1} ΔE_{t+1} u_{x,t+1+j}` (the IS-shock news)
  and `W` the corresponding `u_π` news.
* `valuation_iff` (**unexpected inflation in the full model**): given (9.24)–(9.25) and the spread
  target, (9.22) holds iff `ΔE_{t+1} π_{t+1} = (−σκ ε^{Σs}_{t+1} + κ U + W)/(σκ + ρ)`.
* `output_innov`: hence `ΔE_{t+1} x_{t+1} = [(−σκ ε + κ U + W)/(σκ + ρ) − ΔE_{t+1} u_{π,t+1}]/κ`;
  `ux_enters`: two economies that differ only in `u_x` have output innovations differing by
  `(U − U')/(σκ + ρ)`.
* `coin_ux_moves_output` (**the IS shock moves output**): on the two-coin tree, with no fiscal
  shock and no cost-push shock, an IS shock at date 1 gives an equilibrium of (9.22), (9.24)–(9.25)
  and the spread target whose output innovation is `ρ/(σκ + ρ) · ε_1 ≠ 0`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR5SpreadIS

open Filter Topology SpreadTarget

variable {Ω : Type*} {𝔼 : ExpectationSystem Ω} {σ κ πs β : ℝ} {π x i ux upi : ℕ → Ω → ℝ}

/-- Cochrane (2023), §9.4.1, p. 277: with the spread target `E_t π_{t+1} = π^{e*}`, inflation
dated `t + 2` or later carries no news at `t + 1`: `ΔE_{t+1} π_{t+2+j} = 0`. -/
theorem innov_pi_later (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (t j : ℕ) :
    innov 𝔼 t (π (t + 2 + j)) = 0 := by
  have h1 : ∀ s, s ≤ t + 1 + j → 𝔼.E s (π (t + 2 + j)) = fun _ => πs := fun s hs => by
    have e : t + 2 + j = t + 1 + j + 1 := by ring
    rw [e, ← 𝔼.tower hs, hN.spread (t + 1 + j), 𝔼.const]
  unfold innov
  rw [h1 (t + 1) (by omega), h1 t (by omega), sub_self]

/-- Cochrane (2023), eq. (9.26), p. 277 (corrected form, `SpreadTarget.r_formula`), in news form:
`σ ΔE_{t+1} i_s = (−ΔE_{t+1} π_s + ΔE_{t+1}(u_{π,s} − E_s u_{π,s+1}))/κ + ΔE_{t+1} u_{x,s}`. -/
theorem sigma_innov_i (hκ : κ ≠ 0) (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (t s : ℕ) :
    σ • innov 𝔼 t (i s) = (1 / κ) • (-innov 𝔼 t (π s) +
      innov 𝔼 t (upi s - 𝔼.E s (upi (s + 1)))) + innov 𝔼 t (ux s) := by
  have hr := r_formula hκ hN s
  rw [hN.spread s] at hr
  have hi : σ • i s = (fun _ => σ * πs) + ((1 / κ) • (-(π s - fun _ => πs) +
      (upi s - 𝔼.E s (upi (s + 1)))) + ux s) := by
    rw [← hr]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hlin : ∀ y : Ω → ℝ, innov 𝔼 t (σ • y) = σ • innov 𝔼 t y := fun y => by
    unfold innov
    rw [map_smul, map_smul, smul_sub]
  have hconst : ∀ c : ℝ, innov 𝔼 t (fun _ => c) = 0 := fun c => by
    unfold innov
    rw [𝔼.const, 𝔼.const, sub_self]
  rw [← hlin, hi]
  unfold innov
  simp only [map_add, map_smul, map_neg, map_sub, 𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eq. (9.22), p. 275, with (9.24)–(9.26): each discount-rate term of the
valuation equation, `ρ^{j+1} ΔE_{t+1}(i_{t+1+j} − π_{t+2+j})`, equals
`ρ^{j+1}/σ · [(−[j = 0] ΔE π_{t+1} + ΔE w_{t+1+j})/κ + ΔE u_{x,t+1+j}]`,
`w_s = u_{π,s} − E_s u_{π,s+1}`. -/
theorem discount_term (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hN : FullNK 𝔼 σ κ πs π x i β ux upi)
    (ρ : ℝ) (t j : ℕ) (ω : Ω) :
    ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω =
      ρ ^ (j + 1) / σ * ((-(if j = 0 then innov 𝔼 t (π (t + 1)) ω else 0) +
        innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) / κ +
        innov 𝔼 t (ux (t + 1 + j)) ω) := by
  have hsplit : innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) =
      innov 𝔼 t (i (t + 1 + j)) - innov 𝔼 t (π (t + 2 + j)) := by
    unfold innov
    rw [map_sub, map_sub]
    abel
  have hi := congrFun (sigma_innov_i hκ hN t (t + 1 + j)) ω
  simp only [Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul] at hi
  have hpi : innov 𝔼 t (π (t + 1 + j)) ω = if j = 0 then innov 𝔼 t (π (t + 1)) ω else 0 := by
    rcases j with _ | j
    · simp
    · simp only [Nat.add_one_ne_zero, ↓reduceIte]
      have e : t + 1 + (j + 1) = t + 2 + j := by ring
      rw [e, innov_pi_later hN t j]
      rfl
  rw [hsplit, innov_pi_later hN t j, sub_zero]
  rw [hpi] at hi
  have hA : innov 𝔼 t (i (t + 1 + j)) ω = (1 / κ * (-(if j = 0 then innov 𝔼 t (π (t + 1)) ω
      else 0) + innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) +
      innov 𝔼 t (ux (t + 1 + j)) ω) / σ := by
    rw [eq_div_iff hσ]
    linarith [hi]
  rw [hA]
  ring

/-- Cochrane (2023), eq. (9.22), p. 275, with (9.24)–(9.26) (**the discount-rate terms carry the IS
shock**): if the IS-shock news `U = ∑ ρ^{j+1} ΔE_{t+1} u_{x,t+1+j}` and the cost-push news
`W = ∑ ρ^{j+1} ΔE_{t+1}(u_{π,t+1+j} − E_{t+1+j} u_{π,t+2+j})` are summable at `ω`, then the
discount-rate terms of (9.22) sum to `(−(ρ/κ) ΔE_{t+1} π_{t+1} + U + W/κ)/σ`. -/
theorem discount_terms (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hN : FullNK 𝔼 σ κ πs π x i β ux upi)
    (ρ : ℝ) (t : ℕ) (ω : Ω)
    (hU : Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω)
    (hW : Summable fun j => ρ ^ (j + 1) *
      innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) :
    ∑' j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω =
      (-(ρ / κ) * innov 𝔼 t (π (t + 1)) ω +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω +
        (∑' j, ρ ^ (j + 1) *
          innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) / κ) / σ := by
  set d := innov 𝔼 t (π (t + 1)) ω
  set u : ℕ → ℝ := fun j => ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω with hu
  set w : ℕ → ℝ := fun j => ρ ^ (j + 1) *
    innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω with hw
  set e0 : ℕ → ℝ := fun j => if j = 0 then -(ρ / κ) * d else 0 with he0
  have h0 : HasSum e0 (-(ρ / κ) * d) := hasSum_ite_eq 0 _
  have hterm : ∀ j, ρ ^ (j + 1) * innov 𝔼 t (i (t + 1 + j) - π (t + 2 + j)) ω =
      (e0 j + u j + w j / κ) / σ := fun j => by
    rw [discount_term hσ hκ hN ρ t j ω]
    simp only [he0, hu, hw]
    rcases j with _ | j
    · simp only [↓reduceIte, zero_add, pow_one]
      field_simp
      ring
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, neg_zero, zero_add]
      field_simp
      ring
  have hs := ((h0.add hU.hasSum).add (hW.hasSum.div_const κ)).div_const σ
  rw [tsum_congr hterm, hs.tsum_eq]

/-- Cochrane (2023), eqs. (9.22), (9.24)–(9.26), pp. 275–277 (**unexpected inflation with the
spread target in the full new-Keynesian model**, survey E9.7): given the IS and Phillips curves and
the spread target (`FullNK`), `σ, κ > 0`, `ρ ≥ 0`, and summable IS-shock news `U` and cost-push news
`W`, the valuation equation (9.22) holds iff at every date
`ΔE_{t+1} π_{t+1} = (−σκ ε^{Σs}_{t+1} + κ U + W)/(σκ + ρ)`. The IS shock `u_x` enters unexpected
inflation through the discount-rate terms. -/
theorem valuation_iff {ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (hN : FullNK 𝔼 σ κ πs π x i β ux upi) {ε : ℕ → Ω → ℝ}
    (hU : ∀ t ω, Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω)
    (hW : ∀ t ω, Summable fun j => ρ ^ (j + 1) *
      innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) :
    Valuation 𝔼 ρ π i ε ↔ ∀ t, innov 𝔼 t (π (t + 1)) = fun ω =>
      (-(σ * κ) * ε (t + 1) ω + κ * ∑' j, ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) *
          innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) /
        (σ * κ + ρ) := by
  have hσκ : 0 < σ * κ := mul_pos hσ hκ
  have hD : 0 < σ * κ + ρ := by linarith
  constructor
  · intro hV t
    funext ω
    have h := congrFun (hV t) ω
    simp only [Pi.add_apply, Pi.neg_apply] at h
    rw [discount_terms hσ.ne' hκ.ne' hN ρ t ω (hU t ω) (hW t ω)] at h
    rw [eq_div_iff hD.ne']
    field_simp at h
    linear_combination h
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.neg_apply]
    rw [discount_terms hσ.ne' hκ.ne' hN ρ t ω (hU t ω) (hW t ω)]
    rw [eq_div_iff hD.ne'] at h1
    field_simp
    linear_combination h1

/-- Cochrane (2023), (9.26) first line with (9.22), p. 277 (**output news**, survey E9.7): in any
solution, `ΔE_{t+1} x_{t+1} = [(−σκ ε^{Σs}_{t+1} + κ U + W)/(σκ + ρ) − ΔE_{t+1} u_{π,t+1}]/κ`:
output responds to the IS shock `u_x` through unexpected inflation. -/
theorem output_innov {ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 ≤ ρ)
    (hN : FullNK 𝔼 σ κ πs π x i β ux upi) {ε : ℕ → Ω → ℝ} (hV : Valuation 𝔼 ρ π i ε)
    (hU : ∀ t ω, Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω)
    (hW : ∀ t ω, Summable fun j => ρ ^ (j + 1) *
      innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) (t : ℕ) :
    innov 𝔼 t (x (t + 1)) = fun ω =>
      ((-(σ * κ) * ε (t + 1) ω + κ * ∑' j, ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) *
          innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) /
        (σ * κ + ρ) - innov 𝔼 t (upi (t + 1)) ω) / κ := by
  have hpi := (valuation_iff hσ hκ hρ hN hU hW).1 hV t
  have hx := x_formula hN (t + 1)
  have hlin : innov 𝔼 t (κ • x (t + 1)) = κ • innov 𝔼 t (x (t + 1)) := by
    unfold innov
    rw [map_smul, map_smul, smul_sub]
  have hrhs : innov 𝔼 t ((fun _ => (1 - β) * πs) + (π (t + 1) - fun _ => πs) - upi (t + 1)) =
      innov 𝔼 t (π (t + 1)) - innov 𝔼 t (upi (t + 1)) := by
    unfold innov
    simp only [map_sub, map_add, 𝔼.const]
    abel
  have hxi : κ • innov 𝔼 t (x (t + 1)) = innov 𝔼 t (π (t + 1)) - innov 𝔼 t (upi (t + 1)) := by
    rw [← hlin, hx, hrhs]
  funext ω
  have h := congrFun hxi ω
  rw [hpi] at h
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
  rw [eq_div_iff hκ.ne']
  linarith

/-- Cochrane (2023), §9.4.1, p. 278 (**the IS shock is not irrelevant**, survey E9.7): two economies
with the same expectations, parameters, fiscal shocks `ε^{Σs}` and cost-push shocks `u_π`, but
different IS shocks `u_x, u_x'`, have output innovations differing by `(U − U')/(σκ + ρ)`, where
`U, U'` are the discounted IS-shock news. -/
theorem ux_enters {ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 ≤ ρ) {π' x' i' ux' : ℕ → Ω → ℝ}
    (hN : FullNK 𝔼 σ κ πs π x i β ux upi) (hN' : FullNK 𝔼 σ κ πs π' x' i' β ux' upi)
    {ε : ℕ → Ω → ℝ} (hV : Valuation 𝔼 ρ π i ε) (hV' : Valuation 𝔼 ρ π' i' ε)
    (hU : ∀ t ω, Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω)
    (hU' : ∀ t ω, Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (ux' (t + 1 + j)) ω)
    (hW : ∀ t ω, Summable fun j => ρ ^ (j + 1) *
      innov 𝔼 t (upi (t + 1 + j) - 𝔼.E (t + 1 + j) (upi (t + 1 + j + 1))) ω) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (x (t + 1)) ω - innov 𝔼 t (x' (t + 1)) ω =
      (∑' j, ρ ^ (j + 1) * innov 𝔼 t (ux (t + 1 + j)) ω -
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (ux' (t + 1 + j)) ω) / (σ * κ + ρ) := by
  have h1 := congrFun (output_innov hσ hκ hρ hN hV hU hW t) ω
  have h2 := congrFun (output_innov hσ hκ hρ hN' hV' hU' hW t) ω
  have hD : 0 < σ * κ + ρ := by have := mul_pos hσ hκ; linarith
  rw [h1, h2]
  field_simp
  ring

namespace Coin

/-- Cochrane (2023), §9.4.1, p. 277: the IS shock of the coin example, `u_{x,1} = ε_1` (the first
coin, `±1`) and `u_{x,t} = 0` otherwise. -/
noncomputable def uxC (t : ℕ) (ω : Bool × Bool) : ℝ :=
  if t = 1 then ExpectationsFiniteTree.coinShock 1 ω else 0

/-- Cochrane (2023), §9.4.1, p. 277: the inflation of the coin example,
`π_t = ρκ/(σκ + ρ) · u_{x,t}`. -/
noncomputable def piC (σ κ ρ : ℝ) (t : ℕ) (ω : Bool × Bool) : ℝ :=
  ρ * κ / (σ * κ + ρ) * uxC t ω

/-- Cochrane (2023), §9.4.1, p. 277: output in the coin example, `x_t = π_t/κ` (Phillips curve with
`u_π = 0` and the spread target `π^{e*} = 0`). -/
noncomputable def xC (σ κ ρ : ℝ) (t : ℕ) (ω : Bool × Bool) : ℝ := piC σ κ ρ t ω / κ

/-- Cochrane (2023), eq. (9.24), p. 277: the nominal rate of the coin example, solving the IS curve,
`i_t = E_t π_{t+1} + (E_t x_{t+1} − x_t + u_{x,t})/σ`. -/
noncomputable def iC (σ κ ρ : ℝ) (t : ℕ) : Bool × Bool → ℝ :=
  ExpectationsFiniteTree.coinSystem.E t (piC σ κ ρ (t + 1)) +
    σ⁻¹ • (ExpectationsFiniteTree.coinSystem.E t (xC σ κ ρ (t + 1)) - xC σ κ ρ t + uxC t)

/-- Cochrane (2023), §9.4.1, p. 277: the IS shock is mean zero one date ahead,
`E_t u_{x,t+1} = 0`. -/
theorem E_uxC_succ (t : ℕ) : ExpectationsFiniteTree.coinSystem.E t (uxC (t + 1)) = 0 := by
  rcases t with _ | t
  · have e : uxC 1 = ExpectationsFiniteTree.coinShock 1 := funext fun ω => by simp [uxC]
    rw [e]
    exact ExpectationsFiniteTree.coinShock_mean_zero 0
  · have e : uxC (t + 1 + 1) = 0 := funext fun ω => by simp [uxC]
    rw [e, map_zero]

/-- Cochrane (2023), §9.4.1, p. 277: the IS shock is known when it occurs. -/
theorem E_uxC_self (t : ℕ) : ExpectationsFiniteTree.coinSystem.E t (uxC t) = uxC t := by
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => ?_
  unfold uxC
  split_ifs with ht
  · subst ht
    exact ExpectationsFiniteTree.coinShock_measurable 1 h
  · rfl

/-- Cochrane (2023), §9.4.1, p. 277: `E_t` of a later IS shock (two or more dates ahead) is `0`. -/
theorem E_uxC_later (t j : ℕ) : ExpectationsFiniteTree.coinSystem.E t (uxC (t + 1 + j)) = 0 := by
  rcases j with _ | j
  · exact E_uxC_succ t
  · rw [← ExpectationsFiniteTree.coinSystem.tower (by omega : t ≤ t + 1 + j),
      show t + 1 + (j + 1) = t + 1 + j + 1 by ring, E_uxC_succ, map_zero]

/-- Cochrane (2023), §9.4.1, p. 277: the coin example satisfies the IS curve (9.24), the Phillips
curve (9.25) with `u_π = 0` and the spread target `E_t π_{t+1} = π^{e*} = 0`. -/
theorem fullNK (σ κ ρ β : ℝ) (hσ : σ ≠ 0) (hκ : κ ≠ 0) :
    FullNK ExpectationsFiniteTree.coinSystem σ κ 0 (piC σ κ ρ) (xC σ κ ρ) (iC σ κ ρ) β uxC 0 := by
  have hpi : ∀ t, ExpectationsFiniteTree.coinSystem.E t (piC σ κ ρ (t + 1)) = 0 := fun t => by
    have e : piC σ κ ρ (t + 1) = (ρ * κ / (σ * κ + ρ)) • uxC (t + 1) := funext fun ω => by
      simp [piC]
    rw [e, map_smul, E_uxC_succ, smul_zero]
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · simp only [iC, hpi, zero_add, sub_zero]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hpi]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, xC]
    field_simp
    ring
  · rw [hpi]
    rfl

/-- Cochrane (2023), §9.4.1, p. 277 (**the IS shock moves output**, survey E9.7): on the two-coin
tree, with `σ, κ > 0`, `0 < ρ`, no fiscal shock (`ε^{Σs} = 0`) and no cost-push shock (`u_π = 0`),
an IS shock `u_{x,1} = ε_1` (the first coin) gives a solution of (9.22), (9.24), (9.25) and the
spread target in which unexpected output is `ΔE_1 x_1 = ρ/(σκ + ρ) · ε_1`, which is `ρ/(σκ + ρ) ≠ 0`
at a state where the coin is heads; by `output_innov` every solution has this output innovation. -/
theorem coin_ux_moves_output {σ κ ρ β : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ) :
    FullNK ExpectationsFiniteTree.coinSystem σ κ 0 (piC σ κ ρ) (xC σ κ ρ) (iC σ κ ρ) β uxC 0 ∧
      Valuation ExpectationsFiniteTree.coinSystem ρ (piC σ κ ρ) (iC σ κ ρ) 0 ∧
      innov ExpectationsFiniteTree.coinSystem 0 (xC σ κ ρ 1) =
        (fun ω => ρ / (σ * κ + ρ) * ExpectationsFiniteTree.coinShock 1 ω) ∧
      innov ExpectationsFiniteTree.coinSystem 0 (xC σ κ ρ 1) (true, true) ≠ 0 := by
  have hD : 0 < σ * κ + ρ := by have := mul_pos hσ hκ; linarith
  have hN := fullNK σ κ ρ β hσ.ne' hκ.ne'
  set 𝔼 := ExpectationsFiniteTree.coinSystem with h𝔼
  -- news in the IS shock
  have hinnux : ∀ t j, innov 𝔼 t (uxC (t + 1 + j)) =
      if t = 0 ∧ j = 0 then uxC 1 else 0 := fun t j => by
    unfold innov
    rw [E_uxC_later t j]
    by_cases h : t = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, ↓reduceIte, sub_zero]
      exact E_uxC_self 1
    · simp only [h, ↓reduceIte, sub_zero]
      have hz : uxC (t + 1 + j) = 0 := funext fun ω => by
        simp only [uxC, Pi.zero_apply]
        have : t + 1 + j ≠ 1 := by omega
        simp [this]
      rw [hz, map_zero]
  have hU : ∀ t ω, Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (uxC (t + 1 + j)) ω := by
    intro t ω
    refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    have hj0 : j ≠ 0 := by simpa using hj
    rw [hinnux t j]
    simp [hj0]
  have hW : ∀ t ω, Summable fun j => ρ ^ (j + 1) *
      innov 𝔼 t ((0 : ℕ → Bool × Bool → ℝ) (t + 1 + j) -
        𝔼.E (t + 1 + j) ((0 : ℕ → Bool × Bool → ℝ) (t + 1 + j + 1))) ω := by
    intro t ω
    refine summable_of_ne_finset_zero (s := ∅) fun j _ => ?_
    unfold innov
    simp [map_zero]
  have hpiinn : ∀ t, innov 𝔼 t (piC σ κ ρ (t + 1)) = (ρ * κ / (σ * κ + ρ)) •
      innov 𝔼 t (uxC (t + 1)) := fun t => by
    have e : piC σ κ ρ (t + 1) = (ρ * κ / (σ * κ + ρ)) • uxC (t + 1) := funext fun ω => by
      simp [piC]
    unfold innov
    rw [e, map_smul, map_smul, smul_sub]
  have hV : Valuation 𝔼 ρ (piC σ κ ρ) (iC σ κ ρ) 0 := by
    refine (valuation_iff hσ hκ hρ.le hN hU hW).2 fun t => ?_
    funext ω
    have hzero : ∀ j, ρ ^ (j + 1) * innov 𝔼 t ((0 : ℕ → Bool × Bool → ℝ) (t + 1 + j) -
        𝔼.E (t + 1 + j) ((0 : ℕ → Bool × Bool → ℝ) (t + 1 + j + 1))) ω = 0 := fun j => by
      unfold innov
      simp [map_zero]
    have hsum : ∑' j, ρ ^ (j + 1) * innov 𝔼 t (uxC (t + 1 + j)) ω =
        if t = 0 then ρ * uxC 1 ω else 0 := by
      rw [tsum_eq_single 0 fun j hj => by rw [hinnux t j]; simp [hj]]
      rw [hinnux t 0]
      by_cases ht : t = 0 <;> simp [ht]
    rw [tsum_congr hzero, tsum_zero, hsum, congrFun (hpiinn t) ω]
    have hin1 := congrFun (hinnux t 0) ω
    simp only [add_zero] at hin1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, zero_add, add_zero, hin1]
    by_cases ht : t = 0
    · simp only [ht, and_self, ↓reduceIte]
      field_simp
    · simp only [ht, false_and, ↓reduceIte, Pi.zero_apply, mul_zero, zero_div]
  have hx : innov 𝔼 0 (xC σ κ ρ 1) = fun ω => ρ / (σ * κ + ρ) *
      ExpectationsFiniteTree.coinShock 1 ω := by
    have e : xC σ κ ρ 1 = (ρ / (σ * κ + ρ)) • uxC 1 := funext fun ω => by
      simp only [xC, piC, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hin := hinnux 0 0
    simp only [add_zero, and_self, ↓reduceIte] at hin
    unfold innov at hin ⊢
    rw [e, map_smul, map_smul, ← smul_sub, hin]
    funext ω
    simp [uxC]
  refine ⟨hN, hV, hx, ?_⟩
  rw [hx]
  simp only [ExpectationsFiniteTree.coinShock, ↓reduceIte, mul_one]
  exact (div_pos hρ hD).ne'

end Coin

end Cochrane.AssetsRulesBalanceSheets.TidyR5SpreadIS
