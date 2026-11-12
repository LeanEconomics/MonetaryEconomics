/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR6WelfCalvo
import GainsFromCommitment.Timeless
import GainsFromCommitment.Indexation

/-!
# Propositions 7.1, 7.2 and 7.4 as statements about actual welfare

Woodford (2003), *Interest and Prices*, Chapter 7, §1.1–§1.2, pp. 468–485: Proposition 7.1
(p. 471: discretion, "up to an error of order `O(‖Δ_{−1}^{1/2}, Δ_y, ξ̃‖²)`"), Proposition 7.2
(p. 475: zero inflation is timelessly optimal, "up to an error of order `O(‖Δ_{−1}^{1/2}‖²)`")
and Proposition 7.4 (p. 482: `π_t = γπ_{t−1}`, "up to an error of order
`O(‖Δ_{−1}^{1/2}, π_{−1}‖²)`").

The linear-quadratic content of these propositions is proved in InflationBias, Timeless and
Indexation, with a general weight `λ`. Here they are proved about ACTUAL welfare, the
discounted utility `∑βᵗU_t(ε)` of a one-parameter family of Calvo economies
(`TidyR6WelfCalvo.CalvoFamily`), with the loss weight `λ = κ/θ` produced by the Chapter 6 welfare
expansion (`TidyR6WelfCalvo.lamW`), not assumed. The amplitude `ε` scales the distortions,
the initial dispersion `Δ_{−1}^{1/2}`, `π_{−1}` and the disturbances; the first-order solution of
a family is its plan `(π_t, x_t) = (π₁_{t}, gap₁_t + x*)` in Woodford's variables.

## What "optimal up to an error of order `O(‖·‖²)`" means here

* **Sufficiency.** A family whose first-order plan solves the linear-quadratic problem is at
  least as good as every other admissible family up to `O(ε³)` (`TidyR6WelfCalvo.WeaklyBetter`),
  and strictly better for every small `ε ≠ 0` than every family whose first-order plan differs.
* **Necessity.** A family that is at least as good, up to `O(ε³)`, as one family whose
  first-order plan solves the linear-quadratic problem has itself a first-order plan that solves
  it. Its inflation is therefore the book's expression up to `O(ε²)`: the error of order
  `O(‖·‖²)`.

## Main results

* `prop_7_2_welfare`, `prop_7_2_welfare_unique`: Proposition 7.2.
* `prop_7_1_welfare`, `prop_7_1_welfare_converse` (with `DiscWelfareOpt`): Proposition 7.1,
  discretion as period-by-period optimisation of actual welfare against one-date deviations.
* `prop_7_4_welfare`, `prop_7_4_welfare_converse`: Proposition 7.4 with indexation `γ`.
* Tools: `Assm` (the maintained assumptions), `L_le_of_weaklyBetter`, `weaklyBetter_of_L_le`,
  `lt_of_L_lt`, `qW`, `L_eq`, `gap_bdd`, `L_sub_of_deviation`.
-/

namespace Woodford.GainsFromCommitment.TidyR6WelfProps

open Filter Topology Asymptotics
open Woodford.GainsFromCommitment.TidyR6WelfBase Woodford.GainsFromCommitment.TidyR6WelfBridge
  Woodford.GainsFromCommitment.TidyR6WelfCalvo

variable {Ξ : Type*} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] {ι : Type*} [Fintype ι]

variable (M : BridgeCore.Econ Ξ ι) (α β : ℝ)

/-- Woodford (2003), Ch. 6, §2, pp. 392–402, and Ch. 7, p. 471, fn. 6 (**the maintained
assumptions**, explicit): the economy `M` satisfies the standing assumptions of Chapter 6, the
expansion is at the efficient steady state (`ṽ_y = u_c`; distortions enter through `x*`),
`σ⁻¹ + ω > 0`, `θ > 0`, `1 + ωθ > 0`, `0 < α < 1`, `0 < β < 1`. -/
structure Assm where
  /-- The standing assumptions of Chapter 6. -/
  std : M.Std
  /-- Expansion at the efficient steady state. -/
  eff : M.vy = M.uc
  /-- `σ⁻¹ + ω > 0`. -/
  sig_omg : 0 < M.sig + M.omg
  /-- `θ > 0`. -/
  θ_pos : 0 < M.θ
  /-- `1 + ωθ > 0`. -/
  d_pos : 0 < 1 + M.omg * M.θ
  /-- `α > 0`. -/
  α_pos : 0 < α
  /-- `α < 1`. -/
  α_lt : α < 1
  /-- `β > 0`. -/
  β_pos : 0 < β
  /-- `β < 1`. -/
  β_lt : β < 1

variable {M α β}

/-- Woodford (2003), Ch. 3, (2.19): under `Assm`, `κ > 0`. -/
theorem Assm.kap_pos (A : Assm M α β) : 0 < kap M α β :=
  TidyR6WelfCalvo.kap_pos A.α_pos A.α_lt A.β_lt A.sig_omg A.d_pos

/-- Woodford (2003), Ch. 6, (2.22): under `Assm`, `λ = κ/θ > 0`. -/
theorem Assm.lam_pos (A : Assm M α β) : 0 < lamW M α β :=
  TidyR6WelfCalvo.lamW_pos A.α_pos A.α_lt A.β_lt A.sig_omg A.d_pos A.θ_pos

/-- Woodford (2003), Ch. 6, (2.21): under `Assm`, `Ȳu_c2Θ > 0`. -/
theorem Assm.bK_pos (A : Assm M α β) : 0 < bK M α β :=
  TidyR6WelfCalvo.bK_pos A.std A.α_pos A.α_lt A.β_lt A.θ_pos A.d_pos

variable {γ : ℝ} {ξ1 : ℕ → Ξ} {D0 : ℝ → ℝ}

/-! ### Welfare rankings from first-order losses -/

/-- Woodford (2003), p. 471, fn. 6: if the first-order loss of `F` is no larger than that of `G`
(same disturbances and initial dispersion), `F` is at least as good as `G` up to `O(ε³)`. -/
theorem weaklyBetter_of_L_le (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (F G : CalvoFamily M α γ D0) (h : F.L ξ1 β ≤ G.L ξ1 β) :
    WeaklyBetter (F.W ξ1 β) (G.W ξ1 β) :=
  weaklyBetter_of_loss_le A.bK_pos.le
    (F.bridge ξ1 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt A.β_pos.le
      A.β_lt hξ1)
    (G.bridge ξ1 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt A.β_pos.le
      A.β_lt hξ1) h

/-- Woodford (2003), p. 471, fn. 6 (strict): if the first-order loss of `F` is smaller, `F` is
strictly better than `G` for every small `ε ≠ 0`. -/
theorem lt_of_L_lt (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (F G : CalvoFamily M α γ D0) (h : F.L ξ1 β < G.L ξ1 β) :
    ∀ᶠ ε in 𝓝[≠] (0 : ℝ), G.W ξ1 β ε < F.W ξ1 β ε :=
  eventually_lt_of_loss_lt A.bK_pos
    (F.bridge ξ1 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt A.β_pos.le
      A.β_lt hξ1)
    (G.bridge ξ1 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt A.β_pos.le
      A.β_lt hξ1) h

/-- Woodford (2003), Propositions 7.1–7.4 ("up to an error of order `O(‖·‖²)`", the converse):
if `F` is at least as good as `G` up to `O(ε³)`, its first-order loss is no larger. -/
theorem L_le_of_weaklyBetter (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (F G : CalvoFamily M α γ D0) (h : WeaklyBetter (F.W ξ1 β) (G.W ξ1 β)) :
    F.L ξ1 β ≤ G.L ξ1 β :=
  loss_le_of_weaklyBetter A.bK_pos
    (F.bridge ξ1 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt A.β_pos.le
      A.β_lt hξ1)
    (G.bridge ξ1 A.std A.eff A.sig_omg.ne' A.θ_pos.ne' A.d_pos.ne' A.α_pos A.α_lt A.β_pos.le
      A.β_lt hξ1) h

/-! ### The first-order plan in Woodford's variables -/

/-- Woodford (2003), (1.21), p. 480: quasi-differenced first-order inflation
`π_t − γπ_{t−1} = π₁_{t+1} − γπ₁_t` (Lean date `t + 1` is economic date `t`). -/
def qW (F : CalvoFamily M α γ D0) (t : ℕ) : ℝ := F.π1 (t + 1) - γ * F.π1 t

/-- Woodford (2003), (2.10) and (1.1): the first-order output gap (measured from the efficient
level, i.e. Woodford's `x − x*`) is bounded for bounded disturbances. -/
theorem gap_bdd (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) (F : CalvoFamily M α γ D0) :
    Sequences.Bdd (fun t => M.gap (F.y1 t) (ξ1 t)) := by
  have hx := BridgeCore.unif_of_bounded hξ1
  have h := (BridgeCore.crossMean_isBigO A.std.w_nonneg A.std.w_sum
    (BridgeCore.unif_of_bounded F.y1_bdd)).sub
    (BridgeCore.natLin_isBigO M.sig M.omg (M.gS_isBigO hx) (M.qS_isBigO hx))
  exact BridgeCore.bounded_of_unif (f := fun t => M.gap (F.y1 t) (ξ1 t)) h

omit [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ] in
/-- Woodford (2003), (1.21): the quasi-differenced first-order inflation is bounded. -/
theorem qW_bdd (F : CalvoFamily M α γ D0) : Sequences.Bdd (qW F) := by
  obtain ⟨C, hC⟩ := F.π1_bdd
  refine ⟨C + |γ| * C, fun t => ?_⟩
  unfold qW
  calc |F.π1 (t + 1) - γ * F.π1 t| ≤ |F.π1 (t + 1)| + |γ * F.π1 t| := abs_sub _ _
    _ ≤ C + |γ| * C := by rw [abs_mul]; gcongr <;> exact hC _

/-- Woodford (2003), (1.2)/(1.22), p. 469/481: the first-order loss of a family is the book's
discounted loss of its plan `(q_t, x_t) = (π_t − γπ_{t−1}, gap₁_t + x*)` with `λ = κ/θ`, for any
`x*`. -/
theorem L_eq (F : CalvoFamily M α γ D0) (xs : ℝ) :
    F.L ξ1 β = MonetaryFrictions.dsum β (fun t => qW F t ^ 2 +
      lamW M α β * ((M.gap (F.y1 t) (ξ1 t) + xs) - xs) ^ 2) := by
  unfold CalvoFamily.L MonetaryFrictions.dsum qW
  exact tsum_congr fun t => by ring

/-! ### Proposition 7.2 -/

/-- **Woodford (2003), Proposition 7.2, p. 475, as a statement about actual welfare.** In the
cashless Calvo economy without real disturbances, let `F` be a family whose first-order plan is
zero inflation with output at its natural level (`π₁ ≡ 0`, Woodford's `x ≡ 0`, i.e. the gap from
the efficient level is `−x*`). Then for every family `G` whose first-order plan is feasible
((1.1) with slope `κ`, the Calvo slope of `M`) and satisfies the timeless constraint `π₀ = 0`,
`F` is at least as good as `G` up to `O(ε³)`; and if `G`'s first-order plan is not that of `F`,
`F` is strictly better for every small `ε ≠ 0`. -/
theorem prop_7_2_welfare (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) (xs : ℝ)
    (F G : CalvoFamily M α 0 D0) (hFπ : ∀ t, F.π1 (t + 1) = 0)
    (hFx : ∀ t, M.gap (F.y1 t) (ξ1 t) = -xs)
    (hGas : ∀ t, G.π1 (t + 1) = kap M α β * (M.gap (G.y1 t) (ξ1 t) + xs) + β * G.π1 (t + 2))
    (hG0 : G.π1 1 = 0) :
    WeaklyBetter (F.W ξ1 β) (G.W ξ1 β) ∧
      (¬ ((∀ t, G.π1 (t + 1) = 0) ∧ ∀ t, M.gap (G.y1 t) (ξ1 t) = -xs) →
        ∀ᶠ ε in 𝓝[≠] (0 : ℝ), G.W ξ1 β ε < F.W ξ1 β ε) := by
  have hβ0 := A.β_pos
  have hβ1 := A.β_lt
  have hκ := A.kap_pos
  have hlam := A.lam_pos
  have hLF : F.L ξ1 β = lamW M α β * xs ^ 2 / (1 - β) := by
    rw [L_eq F xs]
    have e : (fun t => qW F t ^ 2 + lamW M α β * ((M.gap (F.y1 t) (ξ1 t) + xs) - xs) ^ 2) =
        fun _ => lamW M α β * xs ^ 2 := by
      funext t
      simp only [qW, hFπ, hFx, zero_mul, sub_zero]
      ring
    rw [e, MonetaryFrictions.dsum_const hβ0.le hβ1]
  have hq : Sequences.Bdd (fun t => G.π1 (t + 1)) := by
    obtain ⟨C, hC⟩ := qW_bdd G
    exact ⟨C, fun t => by simpa [qW] using hC t⟩
  have hx : Sequences.Bdd (fun t => M.gap (G.y1 t) (ξ1 t) + xs) :=
    (gap_bdd A hξ1 G).add (Sequences.bdd_const xs)
  have hLG : G.L ξ1 β = MonetaryFrictions.dsum β (fun t => G.π1 (t + 1) ^ 2 +
      lamW M α β * ((M.gap (G.y1 t) (ξ1 t) + xs) - xs) ^ 2) := by
    rw [L_eq G xs]
    simp only [qW, zero_mul, sub_zero]
  have hmin := Indexation.cashless_timeless_min (xstar := xs) hβ0 hβ1 hκ.ne' hlam.le hq hx
    (fun t => hGas t) hG0
  refine ⟨weaklyBetter_of_L_le A hξ1 F G (by rw [hLF, hLG]; exact hmin), fun hne => ?_⟩
  refine lt_of_L_lt A hξ1 F G (lt_of_le_of_ne (by rw [hLF, hLG]; exact hmin) fun heq => hne ?_)
  have hle : MonetaryFrictions.dsum β (fun t => G.π1 (t + 1) ^ 2 +
      lamW M α β * ((M.gap (G.y1 t) (ξ1 t) + xs) - xs) ^ 2) ≤ lamW M α β * xs ^ 2 / (1 - β) := by
    rw [← hLG, ← heq, hLF]
  obtain ⟨h1, h2⟩ := Indexation.cashless_timeless_unique (xstar := xs) hβ0 hβ1 hκ.ne' hlam hq hx
    (fun t => hGas t) hG0 hle
  exact ⟨fun t => congrFun h1 t, fun t => by have := congrFun h2 t; simp at this; linarith⟩

/-- **Woodford (2003), Proposition 7.2, p. 475 ("the unique policy with this property"), as a
statement about actual welfare.** Let `F` be a family whose first-order plan is a constant
inflation rate `π̄` satisfying (1.1), and `G` a family whose first-order plan solves the
linear-quadratic problem with the constraint `π₀ = π̄` (`Timeless.IsOptimalGivenDet`, weight
`λ = κ/θ`). If `F` is at least as good as `G` up to `O(ε³)` — i.e. the constant target `π̄` is
optimal from a timeless perspective up to third order — then `π̄ = 0`. -/
theorem prop_7_2_welfare_unique (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) (xs pbar : ℝ)
    (F G : CalvoFamily M α 0 D0) (hFπ : ∀ t, F.π1 (t + 1) = pbar)
    (hFas : ∀ t, F.π1 (t + 1) = kap M α β * (M.gap (F.y1 t) (ξ1 t) + xs) + β * F.π1 (t + 2))
    (hGopt : Timeless.IsOptimalGivenDet β (kap M α β) (lamW M α β) xs pbar
      (fun t => G.π1 (t + 1)) (fun t => M.gap (G.y1 t) (ξ1 t) + xs))
    (h : WeaklyBetter (F.W ξ1 β) (G.W ξ1 β)) : pbar = 0 := by
  have hle := L_le_of_weaklyBetter A hξ1 F G h
  have hL : ∀ H : CalvoFamily M α 0 D0, H.L ξ1 β = DateZeroCommitment.detLoss β (lamW M α β) xs
      (fun t => H.π1 (t + 1)) (fun t => M.gap (H.y1 t) (ξ1 t) + xs) := fun H => by
    unfold CalvoFamily.L DateZeroCommitment.detLoss
    exact tsum_congr fun t => by ring
  rw [hL, hL] at hle
  have hFopt : Timeless.IsOptimalGivenDet β (kap M α β) (lamW M α β) xs pbar
      (fun _ => pbar) (fun t => M.gap (F.y1 t) (ξ1 t) + xs) := by
    have hFπ' : (fun t => F.π1 (t + 1)) = fun _ => pbar := funext hFπ
    rw [hFπ'] at hle
    refine ⟨fun t => ?_, ⟨|pbar|, fun _ => le_rfl⟩, ?_, rfl, fun π' x' h1 h2 h3 h4 =>
      hle.trans (hGopt.2.2.2.2 π' x' h1 h2 h3 h4)⟩
    · have := hFas t
      rw [hFπ, hFπ] at this
      exact this
    · obtain ⟨C, hC⟩ := (gap_bdd A hξ1 F).add (Sequences.bdd_const xs)
      exact ⟨C, hC⟩
  exact (Timeless.prop_7_2_det A.β_pos A.β_lt A.kap_pos A.lam_pos pbar).mp ⟨_, hFopt⟩

/-! ### Proposition 7.1: discretion against one-date deviations -/

/-- Woodford (2003), (1.2), p. 469: the period-`t` loss of the first-order plan of a family
without indexation, `π_t² + (κ/θ)(x_t − x*)²` (gap from the efficient level). -/
noncomputable def ell (ξ1 : ℕ → Ξ) (β : ℝ) (F : CalvoFamily M α 0 D0) (t : ℕ) : ℝ :=
  F.π1 (t + 1) ^ 2 + lamW M α β * M.gap (F.y1 t) (ξ1 t) ^ 2

/-- Woodford (2003), (1.2): the period loss of a family is bounded. -/
theorem ell_bdd (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) (F : CalvoFamily M α 0 D0) :
    Sequences.Bdd (ell ξ1 β F) := by
  have hq : Sequences.Bdd (fun t => F.π1 (t + 1)) := by
    obtain ⟨C, hC⟩ := qW_bdd F
    exact ⟨C, fun t => by simpa [qW] using hC t⟩
  exact hq.sq.add ((Sequences.bdd_const _).mul (gap_bdd A hξ1 F).sq)

/-- Woodford (2003), (1.2): without indexation the first-order loss is `∑βᵗℓ_t`. -/
theorem L_eq_ell (F : CalvoFamily M α 0 D0) : F.L ξ1 β = ∑' t, β ^ t * ell ξ1 β F t := by
  unfold CalvoFamily.L ell
  exact tsum_congr fun t => by ring

/-- Woodford (2003), pp. 470–471 (a deviation at one date): if the first-order plans of `F` and
`G` coincide at every date except `t`, then `L_G − L_F = βᵗ(ℓ_t(G) − ℓ_t(F))`. -/
theorem L_sub_of_deviation (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (F G : CalvoFamily M α 0 D0) (t : ℕ)
    (hdev : ∀ s, s ≠ t → G.π1 (s + 1) = F.π1 (s + 1) ∧
      M.gap (G.y1 s) (ξ1 s) = M.gap (F.y1 s) (ξ1 s)) :
    G.L ξ1 β - F.L ξ1 β = β ^ t * (ell ξ1 β G t - ell ξ1 β F t) := by
  rw [L_eq_ell, L_eq_ell]
  have sG := Sequences.summable_disc A.β_pos.le A.β_lt (ell_bdd A hξ1 G).choose_spec
  have sF := Sequences.summable_disc A.β_pos.le A.β_lt (ell_bdd A hξ1 F).choose_spec
  rw [← sG.tsum_sub sF]
  rw [tsum_eq_single t fun s hs => by
    obtain ⟨h1, h2⟩ := hdev s hs
    simp only [ell, h1, h2, sub_self]]
  ring

/-- Woodford (2003), pp. 470–471 (**discretion as optimisation of actual welfare**): the family
`F` is a discretionary optimum up to `O(ε³)` if at every date `t` it is at least as good, up to
`O(ε³)`, as every family `G` that deviates from it only at date `t` (the bank cannot affect other
dates, p. 470) and whose date-`t` first-order point lies on the perceived trade-off (1.3)
`π_t = κx_t + βπᵉ`, with the private expectation `πᵉ = π_{t+1}` of `F`. -/
def DiscWelfareOpt (ξ1 : ℕ → Ξ) (β xs : ℝ) (F : CalvoFamily M α 0 D0) : Prop :=
  ∀ (t : ℕ) (G : CalvoFamily M α 0 D0),
    (∀ s, s ≠ t → G.π1 (s + 1) = F.π1 (s + 1) ∧
      M.gap (G.y1 s) (ξ1 s) = M.gap (F.y1 s) (ξ1 s)) →
    G.π1 (t + 1) = kap M α β * (M.gap (G.y1 t) (ξ1 t) + xs) + β * F.π1 (t + 2) →
      WeaklyBetter (F.W ξ1 β) (G.W ξ1 β)

/-- **Woodford (2003), Proposition 7.1, pp. 471–472, as a statement about actual welfare
(existence).** If the first-order plan of `F` is the Markov equilibrium of the linear-quadratic
game — constant inflation (1.6) `πᵉ = κλx*/((1 − β)λ + κ²)` with `λ = κ/θ` and the output gap
`(1 − β)πᵉ/κ` that (1.1) requires — then `F` is a discretionary optimum up to `O(ε³)`
(`DiscWelfareOpt`), and every one-date deviation on the perceived trade-off with a different
first-order point is strictly worse for every small `ε ≠ 0`. -/
theorem prop_7_1_welfare (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) (xs : ℝ)
    (F : CalvoFamily M α 0 D0)
    (hFπ : ∀ t, F.π1 (t + 1) = InflationBias.discretionInflation β (kap M α β) (lamW M α β) xs)
    (hFx : ∀ t, M.gap (F.y1 t) (ξ1 t) + xs = (1 - β) *
      InflationBias.discretionInflation β (kap M α β) (lamW M α β) xs / kap M α β) :
    DiscWelfareOpt ξ1 β xs F ∧
      ∀ (t : ℕ) (G : CalvoFamily M α 0 D0),
        (∀ s, s ≠ t → G.π1 (s + 1) = F.π1 (s + 1) ∧
          M.gap (G.y1 s) (ξ1 s) = M.gap (F.y1 s) (ξ1 s)) →
        G.π1 (t + 1) = kap M α β * (M.gap (G.y1 t) (ξ1 t) + xs) + β * F.π1 (t + 2) →
        (G.π1 (t + 1) ≠ F.π1 (t + 1) ∨ M.gap (G.y1 t) (ξ1 t) ≠ M.gap (F.y1 t) (ξ1 t)) →
          ∀ᶠ ε in 𝓝[≠] (0 : ℝ), G.W ξ1 β ε < F.W ξ1 β ε := by
  set κ := kap M α β with hκdef
  set lam := lamW M α β with hlamdef
  set p := InflationBias.discretionInflation β κ lam xs with hp
  have hκ : 0 < κ := A.kap_pos
  have hlam : 0 < lam := A.lam_pos
  obtain ⟨πe, hπe, hst⟩ := (InflationBias.prop_7_1 A.β_lt hκ hlam p ((1 - β) * p / κ)).mpr
    ⟨rfl, rfl⟩
  subst hπe
  have hfoc := (InflationBias.static_foc_iff hκ.ne' hlam hst.1).mp hst
  -- the period loss of a deviation exceeds that of `F` by `(κ² + λ)(x' − x̄)²`
  have hdiff : ∀ (t : ℕ) (G : CalvoFamily M α 0 D0),
      G.π1 (t + 1) = κ * (M.gap (G.y1 t) (ξ1 t) + xs) + β * F.π1 (t + 2) →
      ell ξ1 β G t - ell ξ1 β F t =
        (κ ^ 2 + lam) * ((M.gap (G.y1 t) (ξ1 t) + xs) - (1 - β) * p / κ) ^ 2 := by
    intro t G hG
    have hl := InflationBias.staticLoss_line β κ lam xs p ((1 - β) * p / κ)
      (M.gap (G.y1 t) (ξ1 t) + xs)
    rw [← hst.1] at hl
    have e1 : ell ξ1 β G t = InflationBias.staticLoss lam xs
        (κ * (M.gap (G.y1 t) (ξ1 t) + xs) + β * p) (M.gap (G.y1 t) (ξ1 t) + xs) := by
      unfold ell InflationBias.staticLoss
      rw [hG, hFπ]
      ring
    have e2 : ell ξ1 β F t = InflationBias.staticLoss lam xs p ((1 - β) * p / κ) := by
      unfold ell InflationBias.staticLoss
      rw [hFπ]
      have := hFx t
      have hx : M.gap (F.y1 t) (ξ1 t) = (1 - β) * p / κ - xs := by linarith
      rw [hx]
    rw [e1, e2, hl]
    have hk : κ * p + lam * ((1 - β) * p / κ - xs) = 0 := by
      have := hfoc
      field_simp at this ⊢
      linarith
    rw [hk]
    ring
  refine ⟨fun t G hdev hG => ?_, fun t G hdev hG hne => ?_⟩
  · refine weaklyBetter_of_L_le A hξ1 F G ?_
    have h := L_sub_of_deviation A hξ1 F G t hdev
    have := hdiff t G hG
    have : 0 ≤ β ^ t * (ell ξ1 β G t - ell ξ1 β F t) := by
      rw [this]; exact mul_nonneg (pow_nonneg A.β_pos.le t) (by positivity)
    linarith
  · refine lt_of_L_lt A hξ1 F G ?_
    have h := L_sub_of_deviation A hξ1 F G t hdev
    have hd := hdiff t G hG
    have hxne : (M.gap (G.y1 t) (ξ1 t) + xs) - (1 - β) * p / κ ≠ 0 := by
      intro h0
      have hx : M.gap (G.y1 t) (ξ1 t) = M.gap (F.y1 t) (ξ1 t) := by
        have := hFx t; linarith
      have hπ' : G.π1 (t + 1) = F.π1 (t + 1) := by
        have hgx : M.gap (G.y1 t) (ξ1 t) + xs = (1 - β) * p / κ := by linarith
        rw [hG, hFπ, hFπ, hgx]
        field_simp
        ring
      rcases hne with h1 | h1
      · exact h1 hπ'
      · exact h1 hx
    have : 0 < β ^ t * (ell ξ1 β G t - ell ξ1 β F t) := by
      rw [hd]; exact mul_pos (pow_pos A.β_pos t) (by positivity)
    linarith

/-- **Woodford (2003), Proposition 7.1, pp. 471–472, as a statement about actual welfare
(uniqueness: "there is a unique Markov equilibrium ... up to an error of order
`O(‖·‖²)`").** Let `F` have a constant first-order plan `(π̄, x̄)` (Woodford's gap) satisfying
(1.1), and let `G` deviate from `F` only at one date `t`, where its first-order point is the
optimum of the bank's static problem on the perceived trade-off with `πᵉ = π̄`. If `F` is at least
as good as `G` up to `O(ε³)` (in particular if `F` is a discretionary optimum, `DiscWelfareOpt`),
then `π̄` is (1.6) and `x̄ = (1 − β)π̄/κ`, with `λ = κ/θ`. -/
theorem prop_7_1_welfare_converse (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C)
    (xs p xb : ℝ) (F G : CalvoFamily M α 0 D0) (t : ℕ) (hFπ : ∀ s, F.π1 (s + 1) = p)
    (hFx : ∀ s, M.gap (F.y1 s) (ξ1 s) + xs = xb) (hFas : p = kap M α β * xb + β * p)
    (hdev : ∀ s, s ≠ t → G.π1 (s + 1) = F.π1 (s + 1) ∧
      M.gap (G.y1 s) (ξ1 s) = M.gap (F.y1 s) (ξ1 s))
    (hGst : InflationBias.StaticOptimal β (kap M α β) (lamW M α β) xs p (G.π1 (t + 1))
      (M.gap (G.y1 t) (ξ1 t) + xs))
    (h : WeaklyBetter (F.W ξ1 β) (G.W ξ1 β)) :
    p = InflationBias.discretionInflation β (kap M α β) (lamW M α β) xs ∧
      xb = (1 - β) * p / kap M α β := by
  have hle := L_le_of_weaklyBetter A hξ1 F G h
  have hsub := L_sub_of_deviation A hξ1 F G t hdev
  have hβt : 0 < β ^ t := pow_pos A.β_pos t
  have hℓ : ell ξ1 β F t ≤ ell ξ1 β G t := by
    have : 0 ≤ β ^ t * (ell ξ1 β G t - ell ξ1 β F t) := by linarith
    have := (mul_nonneg_iff_of_pos_left hβt).mp this
    linarith
  have hst : InflationBias.StaticOptimal β (kap M α β) (lamW M α β) xs p p xb := by
    refine ⟨hFas, fun x' => ?_⟩
    have e1 : InflationBias.staticLoss (lamW M α β) xs p xb = ell ξ1 β F t := by
      unfold ell InflationBias.staticLoss
      rw [hFπ, ← hFx t]
      ring
    have e2 : ell ξ1 β G t = InflationBias.staticLoss (lamW M α β) xs (G.π1 (t + 1))
        (M.gap (G.y1 t) (ξ1 t) + xs) := by
      unfold ell InflationBias.staticLoss
      ring
    rw [e1]
    exact hℓ.trans (e2 ▸ hGst.2 x')
  exact (InflationBias.prop_7_1 A.β_lt A.kap_pos A.lam_pos p xb).mp ⟨p, rfl, hst⟩

/-! ### Proposition 7.4 -/

/-- **Woodford (2003), Proposition 7.4, pp. 482–483, as a statement about actual welfare.**
With indexation `γ` (the dispersion law (2.24), loss (1.22) with `λ = κ/θ`), let `F` be a family
whose first-order plan follows the rule (1.23) `π_t = γπ_{t−1}` with output at its natural level
(`x ≡ 0`). For every family `G` (same `π_{−1}`-independent t.i.p.) whose first-order plan
satisfies (1.21) and the timeless constraint that (1.23) hold at `t₀`, `F` is at least as good as
`G` up to `O(ε³)`; if `G`'s plan does not follow (1.23) with `x ≡ 0`, `F` is strictly better for
every small `ε ≠ 0`. -/
theorem prop_7_4_welfare (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) (xs : ℝ)
    (F G : CalvoFamily M α γ D0) (hFq : ∀ t, qW F t = 0) (hFx : ∀ t, M.gap (F.y1 t) (ξ1 t) = -xs)
    (hGas : ∀ t, qW G t = kap M α β * (M.gap (G.y1 t) (ξ1 t) + xs) + β * qW G (t + 1))
    (hG0 : qW G 0 = 0) :
    WeaklyBetter (F.W ξ1 β) (G.W ξ1 β) ∧
      (¬ ((∀ t, qW G t = 0) ∧ ∀ t, M.gap (G.y1 t) (ξ1 t) = -xs) →
        ∀ᶠ ε in 𝓝[≠] (0 : ℝ), G.W ξ1 β ε < F.W ξ1 β ε) := by
  have hβ0 := A.β_pos
  have hβ1 := A.β_lt
  have hκ := A.kap_pos
  have hlam := A.lam_pos
  have hLF : F.L ξ1 β = lamW M α β * xs ^ 2 / (1 - β) := by
    rw [L_eq F xs]
    have e : (fun t => qW F t ^ 2 + lamW M α β * ((M.gap (F.y1 t) (ξ1 t) + xs) - xs) ^ 2) =
        fun _ => lamW M α β * xs ^ 2 := by
      funext t
      rw [hFq, hFx]
      ring
    rw [e, MonetaryFrictions.dsum_const hβ0.le hβ1]
  have hx : Sequences.Bdd (fun t => M.gap (G.y1 t) (ξ1 t) + xs) :=
    (gap_bdd A hξ1 G).add (Sequences.bdd_const xs)
  have hmin := Indexation.cashless_timeless_min (xstar := xs) hβ0 hβ1 hκ.ne' hlam.le (qW_bdd G)
    hx hGas hG0
  refine ⟨weaklyBetter_of_L_le A hξ1 F G (by rw [hLF, L_eq G xs]; exact hmin), fun hne => ?_⟩
  refine lt_of_L_lt A hξ1 F G (lt_of_le_of_ne (by rw [hLF, L_eq G xs]; exact hmin)
    fun heq => hne ?_)
  have hle : MonetaryFrictions.dsum β (fun t => qW G t ^ 2 +
      lamW M α β * ((M.gap (G.y1 t) (ξ1 t) + xs) - xs) ^ 2) ≤ lamW M α β * xs ^ 2 / (1 - β) := by
    rw [← L_eq G xs, ← heq, hLF]
  obtain ⟨h1, h2⟩ := Indexation.cashless_timeless_unique (xstar := xs) hβ0 hβ1 hκ.ne' hlam
    (qW_bdd G) hx hGas hG0 hle
  exact ⟨fun t => congrFun h1 t, fun t => by have := congrFun h2 t; simp at this; linarith⟩

/-- **Woodford (2003), Proposition 7.4, pp. 482–483 (the policy "involves a path of inflation
along which (1.23) holds at each date ... up to an error of order `O(‖·‖²)`"), converse.** If
`F`'s first-order plan satisfies (1.21) and the timeless constraint at `t₀`, and `F` is at least
as good, up to `O(ε³)`, as a family `G` following (1.23) with `x ≡ 0`, then `F`'s first-order
plan follows (1.23), `π_t = γπ_{t−1}`, with `x ≡ 0`, at every date. -/
theorem prop_7_4_welfare_converse (A : Assm M α β) (hξ1 : ∃ C, ∀ t, ‖ξ1 t‖ ≤ C) (xs : ℝ)
    (F G : CalvoFamily M α γ D0)
    (hFas : ∀ t, qW F t = kap M α β * (M.gap (F.y1 t) (ξ1 t) + xs) + β * qW F (t + 1))
    (hF0 : qW F 0 = 0) (hGq : ∀ t, qW G t = 0) (hGx : ∀ t, M.gap (G.y1 t) (ξ1 t) = -xs)
    (h : WeaklyBetter (F.W ξ1 β) (G.W ξ1 β)) :
    ∀ t, F.π1 (t + 1) = γ * F.π1 t ∧ M.gap (F.y1 t) (ξ1 t) + xs = 0 := by
  have hβ0 := A.β_pos
  have hβ1 := A.β_lt
  have hle := L_le_of_weaklyBetter A hξ1 F G h
  have hLG : G.L ξ1 β = lamW M α β * xs ^ 2 / (1 - β) := by
    rw [L_eq G xs]
    have e : (fun t => qW G t ^ 2 + lamW M α β * ((M.gap (G.y1 t) (ξ1 t) + xs) - xs) ^ 2) =
        fun _ => lamW M α β * xs ^ 2 := by
      funext t
      rw [hGq, hGx]
      ring
    rw [e, MonetaryFrictions.dsum_const hβ0.le hβ1]
  rw [hLG, L_eq F xs] at hle
  have hx : Sequences.Bdd (fun t => M.gap (F.y1 t) (ξ1 t) + xs) :=
    (gap_bdd A hξ1 F).add (Sequences.bdd_const xs)
  obtain ⟨h1, h2⟩ := Indexation.cashless_timeless_unique (xstar := xs) hβ0 hβ1 A.kap_pos.ne'
    A.lam_pos (qW_bdd F) hx hFas hF0 hle
  intro t
  have e1 := congrFun h1 t
  have e2 := congrFun h2 t
  simp only [qW, Pi.zero_apply] at e1 e2
  exact ⟨by linarith, e2⟩

end Woodford.GainsFromCommitment.TidyR6WelfProps
