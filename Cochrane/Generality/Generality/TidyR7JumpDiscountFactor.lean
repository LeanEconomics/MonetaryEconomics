/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR7ProductStepJumpCoin
import Generality.TidyR7ItoBondStep

/-!
# Jumps: `E_t[d(ΛW)]` with a jumping return, and the innovation of a compensated jump

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6.3, pp. 76–77,
eqs. (3.44)–(3.45) (`dz_t` "can be a compensated jump or a diffusion"), and Online Appendix
A1.5, p. 566 (`E_t[d(Λ_tW_t)] = 0`, written `E_t[dΛ/Λ + dW/W + dΛdW/(ΛW)] = 0`).

## A1.5 with jumps

The cumulative return `W` is adapted, càdlàg and of bounded variation (it may jump); the
discount factor is `Λ = A + M` with `A` càdlàg of bounded variation and `M` a càdlàg martingale
(`TidyR7ProductStepJump.JumpStepData`, from the Monetarism project). Then
(`TidyR7ProductStepJump.JumpStepData.jump_step`) a.s.
`E_s[Λ_tW_t − Λ_sW_s] = E_s∫Λ_− dW + E_s∫W_− dA + E_sΣ_{s<u≤t} ΔΛ_uΔW_u`:
* `jump_pricing_iff`: **`E_t[d(ΛW)] = 0` iff
  `E_s∫Λ_− dW + E_s∫W_− dA + E_s Σ ΔΛΔW = 0`** — the book's `dΛ dW` must be read as the jump
  covariation `ΔΛΔW`;
* `jump_bookForm_iff`: the bracket-free left-point step `E_s[Δ(ΛW)] = E_s∫Λ_− dW + W·E_s dΛ`
  holds iff `E_s[Σ ΔΛΔW] = 0`;
* `coin_jump_step` (non-vacuity, fair coin revealed at `1`, `Λ = M = ξ·1{u ≥ 1}`,
  `W = b + ξ·1{u ≥ 1}`): `E_0[Δ(ΛW)] = 1 = 0 + 0 + 1`, all from the covariation; and
  `coin_jump_bookForm_fails`: the bracket-free form gives `0 ≠ 1`.

## (3.45) with a compensated jump

`innovation_martingale`: if `x_t = x_s + A + c(M_t − M_s)` with `M` a martingale (a compensated
jump or any other `dz` with `E_t dz = 0`), `x_s` `𝓕_s`-measurable, then
`x_t − E_s x_t = c(M_t − M_s) + (A − E_s A)` a.s.; `innovation_martingale_bound`: if `|A| ≤ C`,
`|x_t − E_s x_t − c(M_t − M_s)| ≤ 2C` a.s. No stochastic integral is needed for this.
`coin_innovation` (non-vacuity): for `x = c·M` with the coin jump,
`x_2 − E_0 x_2 = cξ`, which is `±c ≠ 0`.
-/

namespace Cochrane.Generality.TidyR7JumpDiscountFactor

open MeasureTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesIntegral Cochrane.Generality.TidyR7StieltjesSums
  Cochrane.Generality.TidyR7ProductStep Cochrane.Generality.TidyR7ProductStepCoin
  Cochrane.Generality.TidyR7ProductStepJump Cochrane.Generality.TidyR7JumpSums
  Cochrane.Generality.TidyR7ProductStepJumpCoin Cochrane.Generality.TidyR7ItoBondStep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝓕 : Filtration ℝ mΩ}
  {s t : ℝ}

/-! ## A1.5 with a jumping return -/

/-- **Cochrane (2023), A1.5, p. 566, with jumps: `E_t[d(Λ_tW_t)] = 0` iff the expected
increments including the jump covariation sum to zero.** For `W` adapted, càdlàg, of bounded
variation and `Λ = A + M` (hypotheses `TidyR7ProductStepJump.JumpStepData`):
`E_s[W_tΛ_t − W_sΛ_s] = 0` a.s. iff
`E_s∫Λ_− dW + E_s∫W_− dA + E_s Σ_{s<u≤t} ΔΛ_uΔW_u = 0` a.s.
Restates `TidyR7ProductStepJump.JumpStepData.jump_step`. -/
theorem jump_pricing_iff [IsFiniteMeasure μ] {Wr A M : ℝ → Ω → ℝ}
    (hd : JumpStepData μ 𝓕 s t Wr A M) :
    μ[fun ω => Wr t ω * addProc A M t ω - Wr s ω * addProc A M s ω | 𝓕 s] =ᵐ[μ] 0 ↔
      μ[intLeft s t (addProc A M) Wr | 𝓕 s] + μ[intLeft s t Wr A | 𝓕 s] +
        μ[jumpCov s t (addProc A M) Wr | 𝓕 s] =ᵐ[μ] 0 :=
  ⟨fun h => hd.jump_step.symm.trans h, fun h => hd.jump_step.trans h⟩

/-- **Cochrane (2023), A1.5, p. 566, with jumps: the bracket-free step holds iff the jump
covariation has conditional mean zero.** With `W·E_s dΛ := lim E_s[Σ W_iΔΛ_i] = L`
(`TidyR7ProductStep.ExpIncrLimit`): a.s., `E_s[Δ(ΛW)] = E_s∫Λ_− dW + L` iff
`E_s[Σ ΔΛΔW] = 0`.
Restates `TidyR7ProductStepJump.JumpStepData.book_step_iff` in the notation of A1.5. -/
theorem jump_bookForm_iff [IsFiniteMeasure μ] {Wr A M : ℝ → Ω → ℝ}
    (hd : JumpStepData μ 𝓕 s t Wr A M) {L : Ω → ℝ}
    (hL : ExpIncrLimit μ 𝓕 s t Wr (addProc A M) L) :
    ∀ᵐ ω ∂μ, (μ[fun ω => Wr t ω * addProc A M t ω - Wr s ω * addProc A M s ω | 𝓕 s] ω =
        μ[intLeft s t (addProc A M) Wr | 𝓕 s] ω + L ω ↔
      μ[jumpCov s t (addProc A M) Wr | 𝓕 s] ω = 0) :=
  hd.book_step_iff hL

/-- **Cochrane (2023), A1.5, p. 566, with jumps (non-vacuity).** Fair coin `ξ = ±1` revealed at
time `1`, `Λ = M = ξ·1{u ≥ 1}` (a compensated jump), `W = b + ξ·1{u ≥ 1}` (a return that jumps
with `Λ`), on `[0, 2]`: `E_0[Λ_2W_2 − Λ_0W_0] = 1`, `E_0∫Λ_− dW = 0`, `E_0∫W_− dA = 0`,
`E_0[Σ ΔΛΔW] = 1`, and the decomposition holds, `1 = 0 + 0 + 1`. In particular `ΛW` is not
priced (`E_0[d(ΛW)] ≠ 0`), and the whole expected increment is the jump covariation.
Restates `TidyR7ProductStepJumpCoin.jump_corrected`. -/
theorem coin_jump_step (b : ℝ) :
    coinMeasure[fun ω => jumpB b 2 ω * addProc coinA coinM 2 ω -
        jumpB b 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intLeft 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] = 0 ∧
      coinMeasure[intLeft 0 2 (jumpB b) coinA | coinFiltration 0] = 0 ∧
      coinMeasure[jumpCov 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] =
        (fun _ => 1) ∧
      coinMeasure[fun ω => jumpB b 2 ω * addProc coinA coinM 2 ω -
          jumpB b 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[intLeft 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] +
          coinMeasure[intLeft 0 2 (jumpB b) coinA | coinFiltration 0] +
          coinMeasure[jumpCov 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] :=
  jump_corrected b

/-- **Cochrane (2023), A1.5, p. 566, with jumps: dropping `dΛ dW` fails (non-vacuity).** In the
coin economy of `coin_jump_step`, `W·E_0 dΛ = 0` and `E_0[Δ(ΛW)] = 1 ≠ 0 + 0`: the
bracket-free (left-point) step is false when the return jumps with `Λ`.
Restates `TidyR7ProductStepJumpCoin.jump_book_fails`. -/
theorem coin_jump_bookForm_fails (b : ℝ) :
    ExpIncrLimit coinMeasure coinFiltration 0 2 (jumpB b) (addProc coinA coinM) 0 ∧
      coinMeasure[fun ω => jumpB b 2 ω * addProc coinA coinM 2 ω -
          jumpB b 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] ≠
        coinMeasure[intLeft 0 2 (addProc coinA coinM) (jumpB b) | coinFiltration 0] + 0 :=
  ⟨(jump_book_fails b).2.1, (jump_book_fails b).2.2⟩

/-! ## (3.45) with a compensated jump -/

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77, with `dz` a compensated jump (any
martingale).** If `x_t = x_s + A + c(M_t − M_s)` with `M` a martingale for `𝓕`, `s ≤ t`, `x_s`
`𝓕_s`-measurable and integrable and `A` integrable, then a.s.
`x_t − E_s x_t = c(M_t − M_s) + (A − E_s A)`: the innovation is the `dz` part plus the
unexpected part of `A`.
The martingale-driven analogue of `TidyR7ItoInnovation.innovation_eq`. -/
theorem innovation_martingale [IsFiniteMeasure μ] {X M : ℝ → Ω → ℝ} {A : Ω → ℝ} {c : ℝ}
    (hM : Martingale M 𝓕 μ) (hst : s ≤ t) (hXs : StronglyMeasurable[𝓕 s] (X s))
    (hXi : Integrable (X s) μ) (hA : Integrable A μ)
    (hX : ∀ ω, X t ω = X s ω + A ω + c * (M t ω - M s ω)) :
    (fun ω => X t ω - μ[X t | 𝓕 s] ω) =ᵐ[μ]
      fun ω => c * (M t ω - M s ω) + (A ω - μ[A | 𝓕 s] ω) := by
  have iM : Integrable (fun ω => c * (M t ω - M s ω)) μ :=
    ((hM.integrable t).sub (hM.integrable s)).const_mul c
  have hzero : μ[fun ω => c * (M t ω - M s ω) | 𝓕 s] =ᵐ[μ] 0 := by
    have e : (fun ω => c * (M t ω - M s ω)) = c • (M t - M s) := by
      funext ω
      simp [smul_eq_mul]
    rw [e]
    filter_upwards [condExp_smul (μ := μ) (m := 𝓕 s) c (M t - M s),
      condExp_sub (m := 𝓕 s) (hM.integrable t) (hM.integrable s), hM.condExp_ae_eq hst]
      with ω h1 h2 h3
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3,
      condExp_of_stronglyMeasurable (𝓕.le s) (hM.1 s) (hM.integrable s)]
    simp
  have hfun : X t = (fun ω => X s ω + A ω) + fun ω => c * (M t ω - M s ω) := by
    funext ω
    rw [hX ω]
    rfl
  have h1 : μ[X t | 𝓕 s] =ᵐ[μ] μ[fun ω => X s ω + A ω | 𝓕 s] := by
    rw [hfun]
    exact condExp_eq_of_ae_eq_add (ae_of_all _ fun _ => rfl) (hXi.add hA) iM hzero
  have h2 := condExp_add (m := 𝓕 s) hXi hA
  have h3 : μ[X s | 𝓕 s] = X s := condExp_of_stronglyMeasurable (𝓕.le s) hXs hXi
  filter_upwards [h1, h2] with ω e1 e2
  rw [e1, show (fun ω => X s ω + A ω) = X s + A from rfl, e2, Pi.add_apply, h3, hX ω]
  ring

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77, with `dz` a compensated jump: the innovation is
`c dz` up to the unexpected part of `A`.** Under the hypotheses of `innovation_martingale` and
`|A| ≤ C`: `|x_t − E_s x_t − c(M_t − M_s)| ≤ 2C` a.s. (with `A = ∫_s^t μ du`, `C = C_μ(t − s)`).
The martingale-driven analogue of `TidyR7ItoInnovation.innovation_sq_le`. -/
theorem innovation_martingale_bound [IsFiniteMeasure μ] {X M : ℝ → Ω → ℝ} {A : Ω → ℝ}
    {c C : ℝ} (hM : Martingale M 𝓕 μ) (hst : s ≤ t) (hXs : StronglyMeasurable[𝓕 s] (X s))
    (hXi : Integrable (X s) μ) (hA : Integrable A μ) (hAb : ∀ ω, |A ω| ≤ C)
    (hX : ∀ ω, X t ω = X s ω + A ω + c * (M t ω - M s ω)) :
    ∀ᵐ ω ∂μ, |X t ω - μ[X t | 𝓕 s] ω - c * (M t ω - M s ω)| ≤ 2 * C := by
  have hE := ae_bdd_abs_condExp_of_ae_bdd_abs (μ := μ) (m := 𝓕 s) (R := C) (f := A)
    (ae_of_all μ hAb)
  filter_upwards [innovation_martingale hM hst hXs hXi hA hX, hE] with ω h1 h2
  have e : X t ω - μ[X t | 𝓕 s] ω - c * (M t ω - M s ω) = A ω - μ[A | 𝓕 s] ω := by
    linarith [h1]
  rw [e]
  have := abs_sub (A ω) (μ[A | 𝓕 s] ω)
  have h2' : |μ[A | 𝓕 s] ω| ≤ C := h2
  linarith [hAb ω]

/-- **Cochrane (2023), §3.6.3, eq. (3.45), p. 77 (non-vacuity, a compensated jump).** For the
coin martingale `M = ξ·1{u ≥ 1}` and `x = c·M`, the innovation over `[0, 2]` is
`x_2 − E_0 x_2 = cξ` exactly (`= ±c`), the `c dz` of the book with `A = 0`. -/
theorem coin_innovation (c : ℝ) :
    (fun ω => c * coinM 2 ω - coinMeasure[fun ω => c * coinM 2 ω | coinFiltration 0] ω) =
      fun ω => c * coinXi ω := by
  funext ω
  rw [condExp_coin_lt (by norm_num), coinM_ge (by norm_num)]
  simp [coinXi]

end Cochrane.Generality.TidyR7JumpDiscountFactor
