/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralLinks
import OptimalPolicyRules.Prop82General

/-!
# Assumption 8.1 for the basic model

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541), for the basic
neo-Wicksellian model of §3.1 (pp. 582–591), via the second-order multiplier system of
Appendix G.4 (pp. 721–722).

## Main results

* `sys2R_existsUnique`: the second-order Blanchard–Kahn theorem of `IRuleBasic`
  (`sys2_existsUnique`, deterministic initial multipliers) extended to a **random** initial
  multiplier `Φ_{−1}` known at date `0` and bounded: the homogeneous solution
  `Φ̂_s = X^{s+1}Φ_{−1}` carries the initial condition (`hat_sys`), and the rest solves the
  system with `Φ_{−1} = 0`.
* `nk_assumption81M`: **Assumption 8.1 (corrected, `Prop82General.Assumption81M`) holds for the
  basic model**, for every expectation system and every initial date `t₀`: for every bounded
  adapted disturbance and every bounded initial multiplier `M_{t₀−1}` known at `t₀ − 1`, the
  system (1.1) + (1.9) has exactly one bounded solution. The first-order conditions (3.3)–(3.5)
  express `π, x, i` through the multipliers (`GeneralLinks.nk_foc_at_iff`), and (2.1), (3.1) then
  become the multiplier system `P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t` of App. G.4, with dates
  counted from `t₀` (`Prop84General.shiftES`).
* `nk_assumption81_perfectForesight`: under perfect foresight the original formalisation
  `GeneralFOC.LQ.Assumption81` holds as well.
* `not_assumption81_coin`: the original formalisation cannot hold under genuine uncertainty
  from a date `t₀ ≥ 1`: it asks for a solution for every `M_{t₀−1}` known only at `t₀`, while a
  solution has `M_{t₀−1}` known at `t₀ − 1`. On the coin-flip tree it fails at `t₀ = 1` for
  every problem with a forward-looking variable.
-/

namespace Woodford.OptimalPolicyRules.NKAssumption81

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open IRuleBasic (rvMul VAdapted VBounded Sys2 lagV rvMul_rvMul rvMul_add rvMul_sub
  add_rvMul sub_rvMul rvMul_one E_rvMul)

variable {Ω : Type*}

/-! ### The second-order system with a random initial multiplier -/

/-- Woodford (2003), App. G.4, p. 721: a vector process lagged once with a **random** pre-sample
value `z_{−1} = z₀`. -/
def lagR (z0 : Fin 2 → Ω → ℝ) (z : ℕ → Fin 2 → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ
  | 0 => z0
  | s + 1 => z s

/-- Woodford (2003), App. G.4, p. 721: `Φ` solves `P E_sΦ_{s+1} − A₁Φ_s + A₂Φ_{s−1} = F_s` for all
`s ≥ 0`, with the random initial value `Φ_{−1} = Φm`. -/
def Sys2R (𝔼 : ExpectationSystem Ω) (P A1 A2 : Matrix (Fin 2) (Fin 2) ℝ)
    (F : ℕ → Fin 2 → Ω → ℝ) (Φm : Fin 2 → Ω → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ s, rvMul P (fun j => 𝔼.E s (Φ (s + 1) j)) - rvMul A1 (Φ s) + rvMul A2 (lagR Φm Φ s) = F s

/-- Woodford (2003), App. G.4: the homogeneous solution `Φ̂_s = X^{s+1}Φ_{−1}` carrying the
initial multiplier. -/
def hatΦ (X : Matrix (Fin 2) (Fin 2) ℝ) (Φm : Fin 2 → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun s => rvMul (X ^ (s + 1)) Φm

/-- Woodford (2003), App. G.4 (tool): the lag of `Φ̂` is `X^sΦ_{−1}`. -/
theorem lagR_hat (X : Matrix (Fin 2) (Fin 2) ℝ) (Φm : Fin 2 → Ω → ℝ) (s : ℕ) :
    lagR Φm (hatΦ X Φm) s = rvMul (X ^ s) Φm := by
  cases s with
  | zero => simp [lagR, rvMul_one]
  | succ s => rfl

variable (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), App. G.4 (tool): `Φ̂` is known at every date when `Φ_{−1}` is known at `0`. -/
theorem hat_known (X : Matrix (Fin 2) (Fin 2) ℝ) {Φm : Fin 2 → Ω → ℝ}
    (hm : ∀ j, 𝔼.E 0 (Φm j) = Φm j) (k s : ℕ) (j : Fin 2) :
    𝔼.E s (rvMul (X ^ k) Φm j) = rvMul (X ^ k) Φm j := by
  rw [E_rvMul 𝔼]
  congr 1
  funext i
  exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le s) (hm i)

/-- Woodford (2003), App. G.4: `Φ̂_s = X^{s+1}Φ_{−1}` solves the homogeneous system when `X` solves
`PX² − A₁X + A₂ = 0`. -/
theorem hat_sys {P A1 A2 X : Matrix (Fin 2) (Fin 2) ℝ} (hX : P * X * X - A1 * X + A2 = 0)
    {Φm : Fin 2 → Ω → ℝ} (hm : ∀ j, 𝔼.E 0 (Φm j) = Φm j) :
    Sys2R 𝔼 P A1 A2 (fun _ => 0) Φm (hatΦ X Φm) := by
  intro s
  have hE : (fun j => 𝔼.E s (hatΦ X Φm (s + 1) j)) = rvMul (X ^ (s + 2)) Φm :=
    funext fun j => hat_known 𝔼 X hm (s + 2) s j
  rw [hE, lagR_hat, hatΦ, rvMul_rvMul, rvMul_rvMul, rvMul_rvMul, ← sub_rvMul, ← add_rvMul]
  have hm0 : P * X ^ (s + 2) - A1 * X ^ (s + 1) + A2 * X ^ s =
      (P * X * X - A1 * X + A2) * X ^ s := by
    have e1 : X ^ (s + 1) = X * X ^ s := pow_succ' X s
    have e2 : X ^ (s + 2) = X * X * X ^ s := by
      rw [pow_succ', pow_succ', Matrix.mul_assoc]
    rw [e1, e2]
    simp only [sub_mul, add_mul, Matrix.mul_assoc]
  rw [hm0, hX, Matrix.zero_mul]
  funext i ω
  simp [rvMul]

/-- Woodford (2003), App. G.4 (linearity): `Φ` solves the system with the random initial value
`Φ_{−1}` iff `Φ − Φ̂` solves it with `Φ_{−1} = 0` (`IRuleBasic.Sys2`). -/
theorem sys2R_iff {P A1 A2 X : Matrix (Fin 2) (Fin 2) ℝ} (hX : P * X * X - A1 * X + A2 = 0)
    {F : ℕ → Fin 2 → Ω → ℝ} {Φm : Fin 2 → Ω → ℝ} (hm : ∀ j, 𝔼.E 0 (Φm j) = Φm j)
    (Φ : ℕ → Fin 2 → Ω → ℝ) :
    Sys2R 𝔼 P A1 A2 F Φm Φ ↔ Sys2 𝔼 P A1 A2 F 0 (fun s => Φ s - hatΦ X Φm s) := by
  have hh := hat_sys 𝔼 hX hm
  have key : ∀ s, rvMul P (fun j => 𝔼.E s ((Φ (s + 1) - hatΦ X Φm (s + 1)) j)) -
      rvMul A1 (Φ s - hatΦ X Φm s) + rvMul A2 (lagV 0 (fun s => Φ s - hatΦ X Φm s) s) =
      (rvMul P (fun j => 𝔼.E s (Φ (s + 1) j)) - rvMul A1 (Φ s) + rvMul A2 (lagR Φm Φ s)) -
      (rvMul P (fun j => 𝔼.E s (hatΦ X Φm (s + 1) j)) - rvMul A1 (hatΦ X Φm s) +
        rvMul A2 (lagR Φm (hatΦ X Φm) s)) := by
    intro s
    have e1 : (fun j => 𝔼.E s ((Φ (s + 1) - hatΦ X Φm (s + 1)) j)) =
        (fun j => 𝔼.E s (Φ (s + 1) j)) - (fun j => 𝔼.E s (hatΦ X Φm (s + 1) j)) := by
      funext j
      simp [map_sub]
    have e2 : lagV 0 (fun s => Φ s - hatΦ X Φm s) s = lagR Φm Φ s - lagR Φm (hatΦ X Φm) s := by
      cases s with
      | zero =>
        funext j ω
        simp [lagV, lagR]
      | succ s => rfl
    rw [e1, e2, rvMul_sub, rvMul_sub, rvMul_sub]
    abel
  constructor
  · intro h s
    change rvMul P (fun j => 𝔼.E s ((Φ (s + 1) - hatΦ X Φm (s + 1)) j)) -
      rvMul A1 (Φ s - hatΦ X Φm s) + rvMul A2 (lagV 0 (fun s => Φ s - hatΦ X Φm s) s) = F s
    rw [key, h s, hh s, sub_zero]
  · intro h s
    have := key s
    rw [show rvMul P (fun j => 𝔼.E s ((Φ (s + 1) - hatΦ X Φm (s + 1)) j)) -
      rvMul A1 (Φ s - hatΦ X Φm s) + rvMul A2 (lagV 0 (fun s => Φ s - hatΦ X Φm s) s) = F s
      from h s, hh s, sub_zero] at this
    exact this.symm

/-- **Woodford (2003), App. G.4, pp. 721–722: the second-order Blanchard–Kahn theorem with a
random initial multiplier.** Under the hypotheses of `IRuleBasic.sys2_existsUnique` (a stable real
solvent `X`, `B = PX − A₁` invertible, `K = −B⁻¹P` stable), for every bounded adapted forcing and
every bounded `Φ_{−1}` known at date `0` the system has exactly one bounded adapted solution. -/
theorem sys2R_existsUnique {P A1 A2 X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : P * X * X - A1 * X + A2 = 0) (hXs : SchurStable (tr2 X) (det2 X))
    (hB : det2 (P * X - A1) ≠ 0)
    (hK : SchurStable (tr2 (-(IRuleBasic.inv2 (P * X - A1) * P)))
      (det2 (-(IRuleBasic.inv2 (P * X - A1) * P))))
    {F : ℕ → Fin 2 → Ω → ℝ} (hFb : VBounded F) (hFa : VAdapted 𝔼 F) {Φm : Fin 2 → Ω → ℝ}
    (hm : ∀ j, 𝔼.E 0 (Φm j) = Φm j) (hmb : ∃ K, ∀ j ω, |Φm j ω| ≤ K) :
    ∃! Φ, Sys2R 𝔼 P A1 A2 F Φm Φ ∧ VAdapted 𝔼 Φ ∧ VBounded Φ := by
  obtain ⟨Φt, ⟨hs, ha, hb⟩, hu⟩ := IRuleBasic.sys2_existsUnique 𝔼 hX hXs hB hK hFb hFa 0
  have hha : VAdapted 𝔼 (hatΦ X Φm) := fun s j => hat_known 𝔼 X hm (s + 1) s j
  have hhb : VBounded (hatΦ X Φm) := by
    obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hXp⟩ := IRuleBasic.pow_bound_of_schurStable hXs
    obtain ⟨K, hK⟩ := hmb
    have hK' : ∀ j ω, |Φm j ω| ≤ max K 0 := fun j ω => (hK j ω).trans (le_max_left _ _)
    refine ⟨2 * (Cb * max K 0), fun s j ω => ?_⟩
    have h1 := IRuleBasic.abs_rvMul_pow_le hXp (s + 1) hK' j ω
    have hp : ρ ^ (s + 1) ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    have hM : 0 ≤ max K 0 := le_max_right _ _
    have h2 : Cb * ρ ^ (s + 1) * max K 0 ≤ Cb * max K 0 := by
      have := mul_le_mul_of_nonneg_left hp hCb
      nlinarith
    push_cast at h1
    change |rvMul (X ^ (s + 1)) Φm j ω| ≤ _
    linarith
  have hdiff : ∀ Φ : ℕ → Fin 2 → Ω → ℝ, VAdapted 𝔼 Φ → VBounded Φ →
      VAdapted 𝔼 (fun s => Φ s - hatΦ X Φm s) ∧ VBounded (fun s => Φ s - hatΦ X Φm s) := by
    intro Φ h1 h2
    refine ⟨fun s j => ?_, ?_⟩
    · change 𝔼.E s (Φ s j - hatΦ X Φm s j) = Φ s j - hatΦ X Φm s j
      rw [map_sub, h1 s j, hha s j]
    · obtain ⟨M1, hM1⟩ := h2
      obtain ⟨M2, hM2⟩ := hhb
      exact ⟨M1 + M2, fun s j ω => (abs_sub _ _).trans (add_le_add (hM1 s j ω) (hM2 s j ω))⟩
  refine ⟨fun s => Φt s + hatΦ X Φm s, ⟨?_, fun s j => ?_, ?_⟩, ?_⟩
  · rw [sys2R_iff 𝔼 hX hm]
    convert hs using 2
    simp
  · change 𝔼.E s (Φt s j + hatΦ X Φm s j) = Φt s j + hatΦ X Φm s j
    rw [map_add, ha s j, hha s j]
  · obtain ⟨M1, hM1⟩ := hb
    obtain ⟨M2, hM2⟩ := hhb
    exact ⟨M1 + M2, fun s j ω => (abs_add_le _ _).trans (add_le_add (hM1 s j ω) (hM2 s j ω))⟩
  · rintro Φ' ⟨hs', ha', hb'⟩
    obtain ⟨hda, hdb⟩ := hdiff Φ' ha' hb'
    have hd := hu _ ⟨(sys2R_iff 𝔼 hX hm Φ').mp hs', hda, hdb⟩
    funext s
    have := congrFun hd s
    rw [← this]
    abel

/-! ### The basic model -/

namespace NK

open GeneralLinks
open IRuleBasic (Calib PmG A1G A2G cpG c1G c2G Fphi)

variable (c : Calib)

/-- Woodford (2003), App. G.4, pp. 721–722: the multiplier system of the basic model has a real
solvent `X` with both eigenvalues inside the unit circle, `B = PX − A₁` invertible and
`K = −B⁻¹P` stable (from `IRuleBasic.exists_real_split`, `solvent_eq`, `schurStable_scale`). -/
theorem nk_solvent (hc : c.Adm) : ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
    PmG c.β c.σ c.κ c.lx * X * X - A1G c.β c.σ c.κ c.lx c.li * X + A2G c.β c.σ c.κ c.lx = 0 ∧
      SchurStable (tr2 X) (det2 X) ∧
      det2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) ≠ 0 ∧
      SchurStable
        (tr2 (-(IRuleBasic.inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) *
          PmG c.β c.σ c.κ c.lx)))
        (det2 (-(IRuleBasic.inv2 (PmG c.β c.σ c.κ c.lx * X - A1G c.β c.σ c.κ c.lx c.li) *
          PmG c.β c.σ c.κ c.lx))) := by
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩ := hc
  obtain ⟨T, D, hTD, hD, hfacC⟩ := IRuleBasic.exists_real_split hβ0 hβ1 hσ hκ hlx.le hli
  have hfac : ∀ μ : ℝ, IRuleBasic.pR c.β c.σ c.κ c.lx c.li μ =
      (μ ^ 2 - T * μ + D) * (μ ^ 2 - T / (c.β * D) * μ + 1 / (c.β ^ 2 * D)) := by
    intro μ
    have := hfacC μ
    rw [IRuleBasic.pG_ofReal] at this
    exact_mod_cast this
  obtain ⟨-, hsolv, htr, hdet, hB, htrK, hdetK⟩ :=
    IRuleBasic.solvent_eq hβ0 hβ1 hlx hli hTD hD hfac
  have hK := IRuleBasic.schurStable_scale hβ0 hβ1 hTD
  rw [← htrK, ← hdetK] at hK
  exact ⟨_, hsolv, by rw [htr, hdet]; exact hTD, hB, hK⟩

/-- Woodford (2003), (2.1), (3.1) with (3.3)–(3.5), App. G.4: **the rows of the multiplier
system.** If `π, x, i` and their expectations are given by the first-order conditions at `t`
and `t + 1` in terms of the lagged, current and expected multipliers `a, f, e` (entries `0`:
`φ₁` on (3.1), `1`: `φ₂` on (2.1)), the structural equations with disturbance `(c₀, c₁)` hold
iff the two rows of `P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t` do, with `u = −c₀`,
`rⁿ = −c₁/σ`. -/
theorem rows_iff (hc : c.Adm) {a0 a1 f0 f1 e0 e1 p x i ep ex c0 c1 : ℝ}
    (hp : p = c.σ / c.β * a0 - f1 + a1) (hep : ep = c.σ / c.β * f0 - e1 + f1)
    (hx : x = c.xstar + c.lx⁻¹ * (c.κ * f1 - f0 + c.β⁻¹ * a0))
    (hex : ex = c.xstar + c.lx⁻¹ * (c.κ * e1 - e0 + c.β⁻¹ * f0))
    (hi : i = c.istar - c.σ / c.li * f0) :
    (c.β * ep = p - c.κ * x + c0 ∧ c.σ * ep + ex = x + c.σ * i + c1) ↔
      (c.β * e0 + c.β * c.lx * cpG c.σ c.κ c.lx * e1 - c1G c.β c.σ c.lx c.li * f0 -
          c.β * c.lx * cpG c.σ c.κ c.lx * f1 + a0 = c.β * c.lx * c.σ * (-(c1 / c.σ) - c.istar) ∧
        c.β * e1 - cpG c.σ c.κ c.lx * f0 - c2G c.β c.κ c.lx * f1 +
          cpG c.σ c.κ c.lx / c.β * a0 + a1 = -c0 + c.κ * c.xstar) := by
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  obtain ⟨hAS, hIS⟩ := IRuleBasic.rows_real c hc.1.ne' hc.2.2.2.2.1.ne' hc.2.2.2.2.2.ne'
    (u := -c0) (rn := -(c1 / c.σ)) hp hep hx hex hi
  have e1 : (c.β * ep = p - c.κ * x + c0) ↔ (p = c.κ * x + c.β * ep + -c0) :=
    ⟨fun h => by linarith, fun h => by linarith⟩
  have e2 : (c.σ * ep + ex = x + c.σ * i + c1) ↔ (x = ex - c.σ * (i - ep - -(c1 / c.σ))) := by
    constructor
    · intro h
      field_simp
      linarith
    · intro h
      rw [h]
      field_simp
      ring
  rw [e1, e2, hAS, hIS]
  exact and_comm

/-- Woodford (2003), (1.1) for the basic model at one date, p. 537, with any disturbance
`c_t`: the structural equations at `(t, ω)` are `βE_tπ_{t+1} = π_t − κx_t + c₀` (2.1) and
`σE_tπ_{t+1} + E_tx_{t+1} = x_t + σi_t + c₁` (3.1). -/
theorem nk_struct_at (hσ : c.σ ≠ 0) (𝔼 : ExpectationSystem Ω) (cc : ℕ → Ω → Fin 2 → ℝ)
    (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) :
    ((nkSys c hσ).Et *ᵥ EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω =
      (nkSys c hσ).A21 *ᵥ Zpart (y t ω) + (nkSys c hσ).A22 *ᵥ zpart (y t ω) +
        ipart (y t ω) • (nkSys c hσ).B2 + cc t ω) ↔
      (c.β * 𝔼.E t (piOf y (t + 1)) ω = piOf y t ω - c.κ * xOf y t ω + cc t ω 0 ∧
        c.σ * 𝔼.E t (piOf y (t + 1)) ω + 𝔼.E t (xOf y (t + 1)) ω =
          xOf y t ω + c.σ * iOf y t ω + cc t ω 1) := by
  rw [funext_iff, Fin.forall_fin_two]
  simp only [nkSys, mulVec, dotProduct, Fin.sum_univ_two, EV, zpart, Zpart, ipart,
    piOf_eq, xOf_eq, piOf, xOf, iOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Finset.univ_eq_empty, Finset.sum_empty,
    Matrix.zero_apply]
  constructor
  · rintro ⟨h0, h1⟩
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    constructor <;> linarith

/-- Woodford (2003), App. G.4: the multipliers `Φ_s = (φ_{1,t₀+s}, φ_{2,t₀+s})` of a solution of
(1.1) + (1.9), read from `M_{t₀+s}` (`φ_{t₀+s+1}`; entry `1` is the multiplier on (3.1), entry
`0` the one on (2.1)), with dates counted from `t₀`. -/
def PhiOf (t0 : ℕ) (φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun s => ![fun ω => φ (s + t0 + 1) ω (Sum.inr 1), fun ω => φ (s + t0 + 1) ω (Sum.inr 0)]

/-- Woodford (2003), App. G.4: the initial multipliers `Φ_{−1} = (M_{t₀−1,1}, M_{t₀−1,0})`. -/
def PhiM (M0 : Ω → Fin 2 → ℝ) : Fin 2 → Ω → ℝ := ![fun ω => M0 ω 1, fun ω => M0 ω 0]

/-- Woodford (2003), (2.1), (3.1): the forcing of the multiplier system for the disturbance
`c_t = (−u_t, −σrⁿ_t)`, dates counted from `t₀`. -/
noncomputable def Fnk (cc : ℕ → Ω → Fin 2 → ℝ) (t0 : ℕ) : ℕ → Fin 2 → Ω → ℝ :=
  Fphi c (fun s ω => -(cc (s + t0) ω 1 / c.σ)) (fun s ω => -cc (s + t0) ω 0)

/-- Woodford (2003), App. G.4 (tool): the lagged multipliers are those of `φ_{t₀+s}`. -/
theorem lagR_PhiOf (t0 : ℕ) {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} {M0 : Ω → Fin 2 → ℝ}
    (hM : ∀ ω, Mpart (φ t0 ω) = M0 ω) (s : ℕ) :
    lagR (PhiM M0) (PhiOf t0 φ) s =
      ![fun ω => φ (s + t0) ω (Sum.inr 1), fun ω => φ (s + t0) ω (Sum.inr 0)] := by
  cases s with
  | zero =>
    funext j ω
    simp only [zero_add]
    fin_cases j
    · change M0 ω 1 = φ t0 ω (Sum.inr 1)
      rw [← hM ω]
      rfl
    · change M0 ω 0 = φ t0 ω (Sum.inr 0)
      rw [← hM ω]
      rfl
  | succ s =>
    rw [show s + 1 + t0 = s + t0 + 1 by omega]
    rfl

/-- **Woodford (2003), (2.1), (3.1) and (3.3)–(3.5), App. G.4, at one date: (1.1) is the
multiplier system.** Along multipliers with `M_t` known at `t`, if (1.9) holds at `t` and
`t + 1`, then the structural equations at `(t, ω)` hold iff the two rows of
`P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t` do (dates `t = s + t₀`). -/
theorem row_iff (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (cc : ℕ → Ω → Fin 2 → ℝ) (t0 : ℕ)
    (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ}
    {M0 : Ω → Fin 2 → ℝ} (hmφ : MultiplierMeas 𝔼 φ) (hM : ∀ ω, Mpart (φ t0 ω) = M0 ω)
    (hfoc : PFOC (nkProblem c hc) 𝔼 t0 y φ) (s : ℕ) (ω : Ω) :
    ((nkSys c hc.2.2.1.ne').Et *ᵥ EV 𝔼 (s + t0) (fun ω' => zpart (y (s + t0 + 1) ω')) ω =
      (nkSys c hc.2.2.1.ne').A21 *ᵥ Zpart (y (s + t0) ω) +
        (nkSys c hc.2.2.1.ne').A22 *ᵥ zpart (y (s + t0) ω) +
        ipart (y (s + t0) ω) • (nkSys c hc.2.2.1.ne').B2 + cc (s + t0) ω) ↔
      ∀ j, (rvMul (PmG c.β c.σ c.κ c.lx) (fun j => (Prop84General.shiftES 𝔼 t0).E s
          (PhiOf t0 φ (s + 1) j)) - rvMul (A1G c.β c.σ c.κ c.lx c.li) (PhiOf t0 φ s) +
          rvMul (A2G c.β c.σ c.κ c.lx) (lagR (PhiM M0) (PhiOf t0 φ) s)) j ω =
        Fnk c cc t0 s j ω := by
  set t := s + t0 with ht
  have h0 := fun ω' => (nk_foc_at_iff c hc 𝔼 y hmφ t ω').mp (hfoc t (by omega) ω')
  have h1 := fun ω' => (nk_foc_at_iff c hc 𝔼 y hmφ (t + 1) ω').mp (hfoc (t + 1) (by omega) ω')
  simp only [nkPhi1, nkPhi2] at h0 h1
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hlx : c.lx ≠ 0 := hc.2.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  -- the plan at `t + 1` through the multipliers, and its expectation
  have hπf : piOf y (t + 1) = fun ω' => c.σ / c.β * φ (t + 1) ω' (Sum.inr 1) -
      φ (t + 1 + 1) ω' (Sum.inr 0) + φ (t + 1) ω' (Sum.inr 0) := by
    funext ω'
    linarith [(h1 ω').1]
  have hxf : xOf y (t + 1) = fun ω' => c.xstar + c.lx⁻¹ * (c.κ * φ (t + 1 + 1) ω' (Sum.inr 0) -
      φ (t + 1 + 1) ω' (Sum.inr 1) + c.β⁻¹ * φ (t + 1) ω' (Sum.inr 1)) := by
    funext ω'
    have := (h1 ω').2.1
    have h' : xOf y (t + 1) ω' - c.xstar = c.lx⁻¹ * (c.κ * φ (t + 1 + 1) ω' (Sum.inr 0) -
        φ (t + 1 + 1) ω' (Sum.inr 1) + c.β⁻¹ * φ (t + 1) ω' (Sum.inr 1)) := by
      rw [eq_inv_mul_iff_mul_eq₀ hlx]
      linarith
    linarith
  have hk1 := hmφ t 1
  have hk0 := hmφ t 0
  have hEπ : 𝔼.E t (piOf y (t + 1)) ω = c.σ / c.β * φ (t + 1) ω (Sum.inr 1) -
      𝔼.E t (fun ω' => φ (t + 1 + 1) ω' (Sum.inr 0)) ω + φ (t + 1) ω (Sum.inr 0) := by
    rw [hπf, ExpectationTools.E_fun_add, ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul,
      hk1, hk0]
  have hEx : 𝔼.E t (xOf y (t + 1)) ω = c.xstar + c.lx⁻¹ * (c.κ *
      𝔼.E t (fun ω' => φ (t + 1 + 1) ω' (Sum.inr 0)) ω -
      𝔼.E t (fun ω' => φ (t + 1 + 1) ω' (Sum.inr 1)) ω + c.β⁻¹ * φ (t + 1) ω (Sum.inr 1)) := by
    rw [hxf, ExpectationTools.E_fun_add, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add,
      ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_mul, hk1,
      𝔼.const]
  have hp : piOf y t ω = c.σ / c.β * φ t ω (Sum.inr 1) - φ (t + 1) ω (Sum.inr 0) +
      φ t ω (Sum.inr 0) := by linarith [(h0 ω).1]
  have hx : xOf y t ω = c.xstar + c.lx⁻¹ * (c.κ * φ (t + 1) ω (Sum.inr 0) -
      φ (t + 1) ω (Sum.inr 1) + c.β⁻¹ * φ t ω (Sum.inr 1)) := by
    have := (h0 ω).2.1
    have h' : xOf y t ω - c.xstar = c.lx⁻¹ * (c.κ * φ (t + 1) ω (Sum.inr 0) -
        φ (t + 1) ω (Sum.inr 1) + c.β⁻¹ * φ t ω (Sum.inr 1)) := by
      rw [eq_inv_mul_iff_mul_eq₀ hlx]
      linarith
    linarith
  have hi : iOf y t ω = c.istar - c.σ / c.li * φ (t + 1) ω (Sum.inr 1) := by
    have := (h0 ω).2.2
    have h' : iOf y t ω - c.istar = c.li⁻¹ * (-(c.σ * φ (t + 1) ω (Sum.inr 1))) := by
      rw [eq_inv_mul_iff_mul_eq₀ hli]
      linarith
    rw [div_eq_mul_inv]
    linarith
  rw [nk_struct_at c hc.2.2.1.ne' 𝔼 cc y t ω, rows_iff c hc hp hEπ hx hEx hi, Fin.forall_fin_two]
  have hL := lagR_PhiOf t0 hM s
  rw [hL]
  simp only [IRuleBasic.sys_row, PmG, A1G, A2G, Fnk, Fphi, PhiOf, Prop84General.shiftES,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
    smul_eq_mul]
  rw [show s + 1 + t0 + 1 = t + 1 + 1 by omega, show s + t0 + 1 = t + 1 by omega]
  constructor
  · rintro ⟨r0, r1⟩
    constructor <;> linarith
  · rintro ⟨r0, r1⟩
    constructor <;> linarith

/-- **Woodford (2003), (1.1) + (1.9) for the basic model is the multiplier system of App. G.4.**
Along multipliers with `M_t` known at `t`, `M_{t₀−1} = M₀` and (1.9) from `t₀` on, the
structural equations (1.1) hold from `t₀` on iff `Φ` solves
`P E_sΦ_{s+1} − A₁Φ_s + A₂Φ_{s−1} = F_s` (dates `s = t − t₀`, `Φ_{−1}` from `M₀`). -/
theorem struct_iff_sys (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (cc : ℕ → Ω → Fin 2 → ℝ)
    (t0 : ℕ) (y : ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ) {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ}
    {M0 : Ω → Fin 2 → ℝ} (hmφ : MultiplierMeas 𝔼 φ) (hM : ∀ ω, Mpart (φ t0 ω) = M0 ω)
    (hfoc : PFOC (nkProblem c hc) 𝔼 t0 y φ) :
    (nkProblem c hc).sys.Structural 𝔼 cc t0 y ↔
      Sys2R (Prop84General.shiftES 𝔼 t0) (PmG c.β c.σ c.κ c.lx) (A1G c.β c.σ c.κ c.lx c.li)
        (A2G c.β c.σ c.κ c.lx) (Fnk c cc t0) (PhiM M0) (PhiOf t0 φ) := by
  constructor
  · intro h s
    funext j ω
    exact (row_iff c hc 𝔼 cc t0 y hmφ hM hfoc s ω).mp (h (s + t0) (by omega) ω).2 j
  · intro h t ht ω
    obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
    exact ⟨funext fun e => e.elim,
      (row_iff c hc 𝔼 cc t0 y hmφ hM hfoc s ω).mpr fun j => congrFun (congrFun (h s) j) ω⟩

/-- Woodford (2003), App. G.4 (linearity): the difference of two solutions with the same
forcing and initial value solves the homogeneous system with `Φ_{−1} = 0`. -/
theorem sys2R_sub {𝔼 : ExpectationSystem Ω} {P A1 A2 : Matrix (Fin 2) (Fin 2) ℝ}
    {F : ℕ → Fin 2 → Ω → ℝ} {Φm : Fin 2 → Ω → ℝ} {Φ Φ' : ℕ → Fin 2 → Ω → ℝ}
    (h : Sys2R 𝔼 P A1 A2 F Φm Φ) (h' : Sys2R 𝔼 P A1 A2 F Φm Φ') :
    Sys2 𝔼 P A1 A2 (fun _ => 0) 0 (fun s => Φ s - Φ' s) := by
  intro s
  have e1 : (fun j => 𝔼.E s ((fun s => Φ s - Φ' s) (s + 1) j)) =
      (fun j => 𝔼.E s (Φ (s + 1) j)) - (fun j => 𝔼.E s (Φ' (s + 1) j)) := by
    funext j
    simp [map_sub]
  have e2 : lagV 0 (fun s => Φ s - Φ' s) s = lagR Φm Φ s - lagR Φm Φ' s := by
    cases s with
    | zero =>
      funext j ω
      simp [lagV, lagR]
    | succ s => rfl
  rw [e1, e2, rvMul_sub, rvMul_sub, rvMul_sub]
  have hs := h s
  have hs' := h' s
  calc _ = (rvMul P (fun j => 𝔼.E s (Φ (s + 1) j)) - rvMul A1 (Φ s) + rvMul A2 (lagR Φm Φ s)) -
      (rvMul P (fun j => 𝔼.E s (Φ' (s + 1) j)) - rvMul A1 (Φ' s) +
        rvMul A2 (lagR Φm Φ' s)) := by abel
    _ = 0 := by rw [hs, hs', sub_self]

/-- Woodford (2003), App. G.4: the multipliers of a solution of (1.1) + (1.9) are adapted
(dates from `t₀`). -/
theorem phiOf_adapted (𝔼 : ExpectationSystem Ω) (t0 : ℕ) {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) : VAdapted (Prop84General.shiftES 𝔼 t0) (PhiOf t0 φ) := by
  intro s j
  fin_cases j
  · exact hmφ (s + t0) 1
  · exact hmφ (s + t0) 0

/-- Woodford (2003), App. G.4: the multipliers of a bounded solution are bounded. -/
theorem phiOf_bounded (t0 : ℕ) {φ : ℕ → Ω → Empty ⊕ Fin 2 → ℝ} (hb : BoundedV φ) :
    VBounded (PhiOf t0 φ) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M, fun s j ω => ?_⟩
  fin_cases j
  · exact hM (s + t0 + 1) ω (Sum.inr 1)
  · exact hM (s + t0 + 1) ω (Sum.inr 0)

/-- **Woodford (2003), Assumption 8.1 (uniqueness), p. 541, for the basic model**: two bounded
solutions of (1.1) + (1.9) with the same disturbance and the same `M_{t₀−1}` coincide from `t₀`
on (any expectation system, any `t₀`). -/
theorem nk_focUnique (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    FOCUnique (nkProblem c hc) 𝔼 t0 := by
  intro cc Z0 M0 y y' φ φ' hs hs'
  obtain ⟨X, hX, hXs, hB, hK⟩ := nk_solvent c hc
  set 𝔼' := Prop84General.shiftES 𝔼 t0
  have h1 := (struct_iff_sys c hc 𝔼 cc t0 y hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2).mp hs.1.1
  have h2 := (struct_iff_sys c hc 𝔼 cc t0 y' hs'.2.2.1 hs'.2.2.2.1 hs'.2.2.2.2).mp hs'.1.1
  have hd := sys2R_sub h1 h2
  obtain ⟨Z, -, hZu⟩ := IRuleBasic.sys2_existsUnique 𝔼' hX hXs hB hK (F := fun _ => 0)
    ⟨0, fun _ _ _ => by simp⟩ (fun s j => 𝔼'.const s 0) 0
  have hzero : Sys2 𝔼' (PmG c.β c.σ c.κ c.lx) (A1G c.β c.σ c.κ c.lx c.li) (A2G c.β c.σ c.κ c.lx)
      (fun _ => 0) 0 (fun _ => 0) := by
    intro s
    have hE : (fun j => 𝔼'.E s ((fun _ : ℕ => (0 : Fin 2 → Ω → ℝ)) (s + 1) j)) = 0 := by
      funext j
      exact 𝔼'.const s 0
    have hL : lagV 0 (fun _ : ℕ => (0 : Fin 2 → Ω → ℝ)) s = 0 := by
      cases s with
      | zero =>
        funext j ω
        simp [lagV]
      | succ s => rfl
    rw [hE, hL]
    funext j ω
    simp [rvMul]
  have ha1 := phiOf_adapted 𝔼 t0 hs.2.2.1
  have ha2 := phiOf_adapted 𝔼 t0 hs'.2.2.1
  have hDa : VAdapted 𝔼' (fun s => PhiOf t0 φ s - PhiOf t0 φ' s) := by
    intro s j
    change 𝔼'.E s (PhiOf t0 φ s j - PhiOf t0 φ' s j) = PhiOf t0 φ s j - PhiOf t0 φ' s j
    rw [map_sub, ha1 s j, ha2 s j]
  have hDb : VBounded (fun s => PhiOf t0 φ s - PhiOf t0 φ' s) := by
    obtain ⟨M1, hM1⟩ := phiOf_bounded t0 hs.2.1
    obtain ⟨M2, hM2⟩ := phiOf_bounded t0 hs'.2.1
    exact ⟨M1 + M2, fun s j ω => (abs_sub _ _).trans (add_le_add (hM1 s j ω) (hM2 s j ω))⟩
  have hD : (fun s => PhiOf t0 φ s - PhiOf t0 φ' s) = fun _ => 0 := by
    rw [hZu _ ⟨hd, hDa, hDb⟩, hZu _ ⟨hzero, fun s j => 𝔼'.const s 0,
      ⟨0, fun _ _ _ => by simp⟩⟩]
  -- the multipliers agree from `t₀` on
  have hφ : ∀ t, t0 ≤ t → φ t = φ' t := by
    intro t ht
    funext ω r
    rcases r with e | r
    · exact e.elim
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · subst h
        have a := congrFun (hs.2.2.2.1 ω) r
        have b := congrFun (hs'.2.2.2.1 ω) r
        exact a.trans b.symm
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 + 1 := ⟨t - t0 - 1, by omega⟩
        have d0 := congrFun (congrFun (congrFun hD s) 0) ω
        have d1 := congrFun (congrFun (congrFun hD s) 1) ω
        simp only [PhiOf, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
          Pi.zero_apply] at d0 d1
        fin_cases r
        · change φ (s + t0 + 1) ω (Sum.inr 0) = φ' (s + t0 + 1) ω (Sum.inr 0)
          linarith
        · change φ (s + t0 + 1) ω (Sum.inr 1) = φ' (s + t0 + 1) ω (Sum.inr 1)
          linarith
  refine fun t ht => ⟨?_, hφ t ht⟩
  funext ω i
  have g1 := (nk_foc_at_iff c hc 𝔼 y hs.2.2.1 t ω).mp (hs.2.2.2.2 t ht ω)
  have g2 := (nk_foc_at_iff c hc 𝔼 y' hs'.2.2.1 t ω).mp (hs'.2.2.2.2 t ht ω)
  have e0 := congrFun (hφ t ht) ω
  have e1 := congrFun (hφ (t + 1) (by omega)) ω
  simp only [nkPhi1, nkPhi2, e0, e1] at g1 g2
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hlx : c.lx ≠ 0 := hc.2.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  rcases i with (e | j) | u
  · exact e.elim
  · fin_cases j
    · change piOf y t ω = piOf y' t ω
      linarith [g1.1, g2.1]
    · change xOf y t ω = xOf y' t ω
      have h := g1.2.1
      have h' := g2.2.1
      have : c.lx * (xOf y t ω - xOf y' t ω) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hlx
      · linarith
  · change iOf y t ω = iOf y' t ω
    have h := g1.2.2
    have h' := g2.2.2
    have : c.li * (iOf y t ω - iOf y' t ω) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hli
    · linarith

/-- Woodford (2003), fn 6, p. 539 (tool): a linear combination of three quantities bounded by `B`
plus a constant is bounded by `(|a| + |b| + |d|)B + |e|`. -/
theorem abs_lin3 {a b d e u v w B : ℝ} (hu : |u| ≤ B) (hv : |v| ≤ B) (hw : |w| ≤ B) :
    |e + a * u + b * v + d * w| ≤ (|a| + |b| + |d|) * B + |e| := by
  have h1 : |a * u| ≤ |a| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hu (abs_nonneg a)
  have h2 : |b * v| ≤ |b| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hv (abs_nonneg b)
  have h3 : |d * w| ≤ |d| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hw (abs_nonneg d)
  have t1 := abs_add_le (e + a * u + b * v) (d * w)
  have t2 := abs_add_le (e + a * u) (b * v)
  have t3 := abs_add_le e (a * u)
  linarith

/-- Woodford (2003), (3.3)–(3.5): the plan determined by the multipliers `Φ` (dates from `t₀`;
`π_t = σβ⁻¹φ_{1,t−1} − φ_{2t} + φ_{2,t−1}`, `x_t = x* + λ_x⁻¹(κφ_{2t} − φ_{1t} + β⁻¹φ_{1,t−1})`,
`i_t = i* − (σ/λ_i)φ_{1t}`), and `0` before `t₀`. -/
noncomputable def yOf (t0 : ℕ) (M0 : Ω → Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) :
    ℕ → Ω → (Empty ⊕ Fin 2) ⊕ Unit → ℝ :=
  fun t ω => if t0 ≤ t then
    Sum.elim (Sum.elim (fun e => e.elim)
      ![c.σ / c.β * lagR (PhiM M0) Φ (t - t0) 0 ω - Φ (t - t0) 1 ω +
          lagR (PhiM M0) Φ (t - t0) 1 ω,
        c.xstar + c.lx⁻¹ * (c.κ * Φ (t - t0) 1 ω - Φ (t - t0) 0 ω +
          c.β⁻¹ * lagR (PhiM M0) Φ (t - t0) 0 ω)])
      (fun _ => c.istar - c.σ / c.li * Φ (t - t0) 0 ω)
  else 0

/-- Woodford (2003), p. 540: the multipliers `φ_t = M_{t−1}` determined by `Φ` and `M_{t₀−1} = M₀`
(`0` before `t₀`). -/
noncomputable def φOf (t0 : ℕ) (M0 : Ω → Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) :
    ℕ → Ω → Empty ⊕ Fin 2 → ℝ :=
  fun t ω => Sum.elim (fun e => e.elim) (fun j =>
    if t < t0 then 0 else if t = t0 then M0 ω j else ![Φ (t - t0 - 1) 1 ω, Φ (t - t0 - 1) 0 ω] j)

/-- Woodford (2003), App. G.4 (tool): `φOf` has the multipliers `Φ`. -/
theorem phiOf_φOf (t0 : ℕ) (M0 : Ω → Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) :
    PhiOf t0 (φOf t0 M0 Φ) = Φ := by
  funext s j ω
  have h1 : ¬ (s + t0 + 1 < t0) := by omega
  have h2 : s + t0 + 1 ≠ t0 := by omega
  have h3 : s + t0 + 1 - t0 - 1 = s := by omega
  fin_cases j <;> simp [PhiOf, φOf, h1, h2, h3]

/-- Woodford (2003), p. 540 (tool): the lagged multipliers of `φOf` at `t ≥ t₀`. -/
theorem φOf_lag (t0 : ℕ) (M0 : Ω → Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) {t : ℕ} (ht : t0 ≤ t)
    (ω : Ω) : φOf t0 M0 Φ t ω (Sum.inr 1) = lagR (PhiM M0) Φ (t - t0) 0 ω ∧
      φOf t0 M0 Φ t ω (Sum.inr 0) = lagR (PhiM M0) Φ (t - t0) 1 ω := by
  rcases Nat.eq_or_lt_of_le ht with h | h
  · subst h
    simp [φOf, lagR, PhiM]
  · obtain ⟨k, hk⟩ : ∃ k, t - t0 = k + 1 := ⟨t - t0 - 1, by omega⟩
    have h1 : ¬ t < t0 := by omega
    have h2 : t ≠ t0 := by omega
    simp [φOf, h1, h2, hk, lagR]

/-- Woodford (2003), p. 540 (tool): the current multipliers of `φOf` at `t ≥ t₀`. -/
theorem φOf_succ (t0 : ℕ) (M0 : Ω → Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) {t : ℕ} (ht : t0 ≤ t)
    (ω : Ω) : φOf t0 M0 Φ (t + 1) ω (Sum.inr 1) = Φ (t - t0) 0 ω ∧
      φOf t0 M0 Φ (t + 1) ω (Sum.inr 0) = Φ (t - t0) 1 ω := by
  have h1 : ¬ t + 1 < t0 := by omega
  have h2 : t + 1 ≠ t0 := by omega
  have h3 : t + 1 - t0 - 1 = t - t0 := by omega
  simp [φOf, h1, h2, h3]

/-- **Woodford (2003), Assumption 8.1 (existence, corrected), p. 541, for the basic model**: for
every bounded adapted disturbance and every bounded `M_{t₀−1}` known at `t₀ − 1`, (1.1) + (1.9)
has a bounded solution (any expectation system, any `t₀`). The multipliers solve the system of
App. G.4 with the random initial value (`sys2R_existsUnique`); the plan is read off (3.3)–(3.5). -/
theorem nk_focSolvableM (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Prop82General.FOCSolvableM (nkProblem c hc) 𝔼 t0 := by
  intro cc Z0 M0 hcb hca _ hMb hMk
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hlx : c.lx ≠ 0 := hc.2.2.2.2.1.ne'
  have hli : c.li ≠ 0 := hc.2.2.2.2.2.ne'
  obtain ⟨X, hX, hXs, hB, hK⟩ := nk_solvent c hc
  set 𝔼' := Prop84General.shiftES 𝔼 t0 with h𝔼'
  have hMk0 : ∀ j, 𝔼'.E 0 (PhiM M0 j) = PhiM M0 j := by
    intro j
    have h := KnownV.mono 𝔼 (Nat.sub_le t0 1) hMk
    fin_cases j
    · change 𝔼.E (0 + t0) (fun ω => M0 ω 1) = fun ω => M0 ω 1
      rw [zero_add]
      exact h 1
    · change 𝔼.E (0 + t0) (fun ω => M0 ω 0) = fun ω => M0 ω 0
      rw [zero_add]
      exact h 0
  obtain ⟨K, hK0⟩ := hMb
  have hMb' : ∃ K, ∀ j ω, |PhiM M0 j ω| ≤ K := by
    refine ⟨K, fun j ω => ?_⟩
    fin_cases j
    · exact hK0 ω 1
    · exact hK0 ω 0
  -- the forcing
  obtain ⟨Mc, hMc⟩ := hcb
  have hFb : VBounded (Fnk c cc t0) := by
    refine IRuleBasic.Fphi_bounded c ⟨Mc / |c.σ|, fun s ω => ?_⟩ ⟨Mc, fun s ω => ?_⟩
    · rw [abs_neg, abs_div]
      exact div_le_div_of_nonneg_right (hMc (s + t0) ω 1) (abs_nonneg _)
    · rw [abs_neg]
      exact hMc (s + t0) ω 0
  have hFa : VAdapted 𝔼' (Fnk c cc t0) := by
    refine IRuleBasic.Fphi_adapted 𝔼' c (fun s => ?_) (fun s => ?_)
    · change 𝔼.E (s + t0) (fun ω => -(cc (s + t0) ω 1 / c.σ)) = _
      have e : (fun ω => -(cc (s + t0) ω 1 / c.σ)) =
          (-c.σ⁻¹) • fun ω => cc (s + t0) ω 1 := by
        funext ω
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, map_smul, hca (s + t0) 1]
    · change 𝔼.E (s + t0) (fun ω => -cc (s + t0) ω 0) = _
      have e : (fun ω => -cc (s + t0) ω 0) = -fun ω => cc (s + t0) ω 0 := rfl
      rw [e, map_neg, hca (s + t0) 0]
  obtain ⟨Φ, ⟨hΦs, hΦa, hΦb⟩, -⟩ := sys2R_existsUnique 𝔼' hX hXs hB hK hFb hFa hMk0 hMb'
  set φ := φOf t0 M0 Φ with hφdef
  set y := yOf c t0 M0 Φ with hydef
  -- the multipliers
  have hM : ∀ ω, Mpart (φ t0 ω) = M0 ω := by
    intro ω
    funext j
    simp [hφdef, φOf, Mpart]
  have hmφ : MultiplierMeas 𝔼 φ := by
    intro t r
    rcases lt_trichotomy (t + 1) t0 with h | h | h
    · have e : (fun ω => φ (t + 1) ω (Sum.inr r)) = fun _ => 0 := by
        funext ω
        simp [hφdef, φOf, h]
      rw [e, 𝔼.const]
    · have e : (fun ω => φ (t + 1) ω (Sum.inr r)) = fun ω => M0 ω r := by
        funext ω
        simp [hφdef, φOf, h]
      rw [e]
      have := hMk r
      rwa [show t0 - 1 = t by omega] at this
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
      have hs := φOf_succ t0 M0 Φ (t := s + t0) (by omega)
      rw [Nat.add_sub_cancel] at hs
      fin_cases r
      · have e : (fun ω => φ (s + t0 + 1) ω (Sum.inr 0)) = Φ s 1 := funext fun ω => (hs ω).2
        change 𝔼.E (s + t0) (fun ω => φ (s + t0 + 1) ω (Sum.inr 0)) =
          fun ω => φ (s + t0 + 1) ω (Sum.inr 0)
        rw [e]
        exact hΦa s 1
      · have e : (fun ω => φ (s + t0 + 1) ω (Sum.inr 1)) = Φ s 0 := funext fun ω => (hs ω).1
        change 𝔼.E (s + t0) (fun ω => φ (s + t0 + 1) ω (Sum.inr 1)) =
          fun ω => φ (s + t0 + 1) ω (Sum.inr 1)
        rw [e]
        exact hΦa s 0
  -- bounds
  obtain ⟨MΦ, hMΦ⟩ := hΦb
  set Bd := max MΦ (max K 0) with hBd
  have hΦB : ∀ s j ω, |Φ s j ω| ≤ Bd := fun s j ω => (hMΦ s j ω).trans (le_max_left _ _)
  have hLB : ∀ s j ω, |lagR (PhiM M0) Φ s j ω| ≤ Bd := by
    intro s j ω
    cases s with
    | zero =>
      fin_cases j
      · exact (hK0 ω 1).trans ((le_max_left _ _).trans (le_max_right _ _))
      · exact (hK0 ω 0).trans ((le_max_left _ _).trans (le_max_right _ _))
    | succ s => exact hΦB s j ω
  have hB0 : 0 ≤ Bd := (le_max_right K 0).trans (le_max_right _ _)
  have hφb : BoundedV φ := by
    refine ⟨Bd, fun t ω r => ?_⟩
    rcases r with e | r
    · exact e.elim
    · by_cases h1 : t < t0
      · simp [hφdef, φOf, h1, hB0]
      · by_cases h2 : t = t0
        · subst h2
          simp only [hφdef, φOf, lt_irrefl, ↓reduceIte, Sum.elim_inr]
          exact (hK0 ω r).trans ((le_max_left _ _).trans (le_max_right _ _))
        · simp only [hφdef, φOf, h1, h2, ↓reduceIte, Sum.elim_inr]
          fin_cases r
          · exact hΦB _ 1 ω
          · exact hΦB _ 0 ω
  -- the first-order conditions
  have hfoc : PFOC (nkProblem c hc) 𝔼 t0 y φ := by
    intro t ht ω
    refine (nk_foc_at_iff c hc 𝔼 y hmφ t ω).mpr ?_
    obtain ⟨l1, l0⟩ := φOf_lag t0 M0 Φ ht ω
    obtain ⟨s1, s0⟩ := φOf_succ t0 M0 Φ ht ω
    simp only [nkPhi1, nkPhi2, hφdef, l1, l0, s1, s0, hydef, piOf_eq, xOf_eq, iOf, yOf, ht,
      ↓reduceIte, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨by ring, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring
  -- the structural equations
  have hstr : (nkProblem c hc).sys.Structural 𝔼 cc t0 y := by
    refine (struct_iff_sys c hc 𝔼 cc t0 y hmφ hM hfoc).mpr ?_
    rw [hφdef, phiOf_φOf]
    exact hΦs
  -- the plan is bounded and adapted
  have hyb : BoundedV y := by
    refine ⟨((|c.σ / c.β| + 1 + 1) * Bd + 0) + ((|c.lx⁻¹ * c.κ| + |c.lx⁻¹| + |c.lx⁻¹ * c.β⁻¹|) *
      Bd + |c.xstar|) + ((|c.σ / c.li| + 0 + 0) * Bd + |c.istar|), fun t ω i => ?_⟩
    have hb1 := abs_lin3 (e := 0) (a := c.σ / c.β) (b := -1) (d := 1)
      (hLB (t - t0) 0 ω) (hΦB (t - t0) 1 ω) (hLB (t - t0) 1 ω)
    have hb2 := abs_lin3 (e := c.xstar) (a := c.lx⁻¹ * c.κ) (b := -c.lx⁻¹)
      (d := c.lx⁻¹ * c.β⁻¹) (hΦB (t - t0) 1 ω) (hΦB (t - t0) 0 ω) (hLB (t - t0) 0 ω)
    have hb3 := abs_lin3 (e := c.istar) (a := -(c.σ / c.li)) (b := 0) (d := 0)
      (hΦB (t - t0) 0 ω) (hΦB (t - t0) 0 ω) (hΦB (t - t0) 0 ω)
    simp only [abs_neg, abs_one, abs_zero] at hb1 hb2 hb3
    have p1 : 0 ≤ ((|c.σ / c.β| + 1 + 1) * Bd + 0) := by positivity
    have p2 : 0 ≤ (|c.lx⁻¹ * c.κ| + |c.lx⁻¹| + |c.lx⁻¹ * c.β⁻¹|) * Bd + |c.xstar| := by
      positivity
    have p3 : 0 ≤ (|c.σ / c.li| + 0 + 0) * Bd + |c.istar| := by positivity
    by_cases ht : t0 ≤ t
    · rcases i with (e | j) | u
      · exact e.elim
      · fin_cases j
        · change |y t ω (Sum.inl (Sum.inr 0))| ≤ _
          simp only [hydef, yOf, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr,
            Matrix.cons_val_zero]
          have e : c.σ / c.β * lagR (PhiM M0) Φ (t - t0) 0 ω - Φ (t - t0) 1 ω +
              lagR (PhiM M0) Φ (t - t0) 1 ω = 0 + c.σ / c.β * lagR (PhiM M0) Φ (t - t0) 0 ω +
              -1 * Φ (t - t0) 1 ω + 1 * lagR (PhiM M0) Φ (t - t0) 1 ω := by ring
          rw [e]
          linarith
        · change |y t ω (Sum.inl (Sum.inr 1))| ≤ _
          simp only [hydef, yOf, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr,
            Matrix.cons_val_one, Matrix.cons_val_zero]
          have e : c.xstar + c.lx⁻¹ * (c.κ * Φ (t - t0) 1 ω - Φ (t - t0) 0 ω +
              c.β⁻¹ * lagR (PhiM M0) Φ (t - t0) 0 ω) = c.xstar + c.lx⁻¹ * c.κ * Φ (t - t0) 1 ω +
              -c.lx⁻¹ * Φ (t - t0) 0 ω + c.lx⁻¹ * c.β⁻¹ * lagR (PhiM M0) Φ (t - t0) 0 ω := by
            ring
          rw [e]
          linarith
      · simp only [hydef, yOf, ht, ↓reduceIte, Sum.elim_inr]
        have e : c.istar - c.σ / c.li * Φ (t - t0) 0 ω = c.istar + -(c.σ / c.li) *
            Φ (t - t0) 0 ω + 0 * Φ (t - t0) 0 ω + 0 * Φ (t - t0) 0 ω := by ring
        rw [e]
        linarith
    · simp only [hydef, yOf, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      linarith
  have hlagk : ∀ s j, 𝔼.E (s + t0) (lagR (PhiM M0) Φ s j) = lagR (PhiM M0) Φ s j := by
    intro s j
    cases s with
    | zero => rw [zero_add]; exact (zero_add t0) ▸ hMk0 j
    | succ k =>
      exact ForwardSolution.E_of_known 𝔼 (by omega : k + t0 ≤ k + 1 + t0) (hΦa k j)
  have hΦk : ∀ s j, 𝔼.E (s + t0) (Φ s j) = Φ s j := fun s j => hΦa s j
  have hya : AdaptedV 𝔼 y := by
    intro t i
    by_cases ht : t0 ≤ t
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + t0 := ⟨t - t0, by omega⟩
      have hs : s + t0 - t0 = s := by omega
      rcases i with (e | j) | u
      · exact e.elim
      · fin_cases j
        · have e : (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 0))) =
              (c.σ / c.β) • lagR (PhiM M0) Φ s 0 - Φ s 1 + lagR (PhiM M0) Φ s 1 := by
            funext ω
            simp [hydef, yOf, hs]
          change 𝔼.E (s + t0) (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 0))) =
            fun ω => y (s + t0) ω (Sum.inl (Sum.inr 0))
          rw [e, map_add, map_sub, map_smul, hlagk, hlagk, hΦk]
        · have e : (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 1))) =
              (fun _ => c.xstar) + c.lx⁻¹ • (c.κ • Φ s 1 - Φ s 0 +
                c.β⁻¹ • lagR (PhiM M0) Φ s 0) := by
            funext ω
            simp [hydef, yOf, hs]
            ring
          change 𝔼.E (s + t0) (fun ω => y (s + t0) ω (Sum.inl (Sum.inr 1))) =
            fun ω => y (s + t0) ω (Sum.inl (Sum.inr 1))
          rw [e, map_add, map_smul, map_add, map_sub, map_smul, map_smul, hlagk, hΦk, hΦk,
            𝔼.const]
      · have e : (fun ω => y (s + t0) ω (Sum.inr u)) =
            (fun _ => c.istar) - (c.σ / c.li) • Φ s 0 := by
          funext ω
          simp [hydef, yOf, hs]
        change 𝔼.E (s + t0) (fun ω => y (s + t0) ω (Sum.inr u)) =
          fun ω => y (s + t0) ω (Sum.inr u)
        rw [e, map_sub, map_smul, hΦk, 𝔼.const]
    · have e : (fun ω => y t ω i) = fun _ => 0 := by
        funext ω
        simp [hydef, yOf, ht]
      change 𝔼.E t (fun ω => y t ω i) = fun ω => y t ω i
      rw [e, 𝔼.const]
  exact ⟨y, φ, ⟨hstr, fun _ => funext fun e => e.elim, hyb, hya⟩, hφb, hmφ, hM, hfoc⟩

/-- **Woodford (2003), Assumption 8.1, p. 541, holds for the basic model** in the corrected form
`Prop82General.Assumption81M`: for every expectation system, every initial date `t₀`, every
bounded adapted disturbance and every bounded `M_{t₀−1}` known at `t₀ − 1`, the system
(1.1) + (1.9) has exactly one bounded solution. -/
theorem nk_assumption81M (hc : c.Adm) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Prop82General.Assumption81M (nkProblem c hc) 𝔼 t0 :=
  ⟨nk_focSolvableM c hc 𝔼 t0, nk_focUnique c hc 𝔼 t0⟩

/-- **Woodford (2003), Assumption 8.1, p. 541, for the basic model under perfect foresight**, in
the original formalisation `GeneralFOC.LQ.Assumption81` (every initial condition is known and
bounded on the one-point sample space). -/
theorem nk_assumption81_perfectForesight (hc : c.Adm) (t0 : ℕ) :
    Assumption81 (nkProblem c hc) perfectForesight t0 := by
  refine ⟨fun cc Z0 M0 hcb hca hZ0 _ => ?_, nk_focUnique c hc perfectForesight t0⟩
  exact nk_focSolvableM c hc perfectForesight t0 cc Z0 M0 hcb hca hZ0
    ⟨|M0 () 0| + |M0 () 1|, fun ω r => by
      rcases ω
      fin_cases r
      · simp
      · simp⟩ (fun _ => rfl)

end NK

/-! ### The original formalisation of Assumption 8.1 under uncertainty -/

/-- **Woodford (2003), Assumption 8.1, p. 541: the original formalisation
`GeneralFOC.LQ.Assumption81` fails under genuine uncertainty from `t₀ = 1`**, for every problem
with a forward-looking variable. It asks for a solution for every `M_{t₀−1}` known at `t₀`, but a
solution has `M_t` known at `t` (`MultiplierMeas`), so `M_{t₀−1}` must be known at `t₀ − 1`; on the
coin-flip tree the first flip `ε₁` is known at date 1 and not at date 0. Hence the corrected
`Prop82General.Assumption81M` (initial multiplier bounded and known at `t₀ − 1`). -/
theorem not_assumption81_coin {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ]
    [DecidableEq ιZ] [DecidableEq ιz] [Nonempty ιz] (P : LQProblem ιZ ιz ιτ) :
    ¬ Assumption81 P ExpectationsFiniteTree.coinSystem 1 := by
  intro hA
  obtain ⟨r⟩ := (inferInstance : Nonempty ιz)
  have hk : KnownV ExpectationsFiniteTree.coinSystem 1
      (fun ω (_ : ιz) => ExpectationsFiniteTree.coinShock 1 ω) := by
    intro j
    funext ω
    rw [ExpectationsFiniteTree.coinSystem,
      ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' hω' =>
      ExpectationsFiniteTree.coinShock_measurable 1 hω'
  obtain ⟨y, φ, hs⟩ := hA.solvable (fun _ _ _ => 0) (fun _ _ => 0)
    (fun ω _ => ExpectationsFiniteTree.coinShock 1 ω) ⟨0, fun _ _ _ => by simp⟩
    (fun t _ => ExpectationsFiniteTree.coinSystem.const t 0)
    (fun _ => ExpectationsFiniteTree.coinSystem.const 1 0) hk
  have hm := hs.2.2.1 0 r
  have hM : (fun ω => φ (0 + 1) ω (Sum.inr r)) = ExpectationsFiniteTree.coinShock 1 := by
    funext ω
    exact congrFun (hs.2.2.2.1 ω) r
  rw [hM, ExpectationsFiniteTree.coinShock_mean_zero 0] at hm
  have := congrFun hm (true, true)
  simp [ExpectationsFiniteTree.coinShock] at this

end Woodford.OptimalPolicyRules.NKAssumption81
