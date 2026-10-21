/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.ISBlock
import PolicyResponseDynamics.ForwardSystems
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Capital and the natural rate of interest

Woodford (2003), *Interest and Prices*, Chapter 5, §3.4, pp. 372–378, and Appendix D.3,
pp. 690–691 (Proposition 5.2).

The natural rates are those of the flexible-price equilibrium given the actual capital stock;
they are taken (as the book does on p. 373) to be affine in it (`NaturalAffine`), which is the
explicit hypothesis behind Proposition 5.2. Equations (3.7)–(3.10), (3.18) are taken from the
linearisation as given (see `ISBlock`). Everything holds for an arbitrary `ExpectationSystem`.

## Main results

* `prop52`: **Proposition 5.2, corrected** (survey error 2). (3.28)/(D.7) is printed without its
  left-hand side and without the `λ̃` terms; the equation that the proof of D.3 actually yields
  (and that holds iff the sticky-price (3.7) holds, given the flexible-price (3.7)) is
  `λ̃_t + ε_ψK̃_{t+1} = β(1−δ)E_t(λ̃_{t+1} + η_λK̃_{t+1}) + c'[ρ_yE_t(Ỹ_{t+1} + η_yK̃_{t+1})
  − ρ_kK̃_{t+1}] + βε_ψ[E_t(K̃_{t+2} + η_kK̃_{t+1}) − K̃_{t+1}]`.
  `flex_value`, `flex_expectation`: the D.3 step `E_t Xⁿ_{t+1} − η_X K̃_{t+1}`.
  `printed328_false`: the printed expression is neither zero nor equal to `λ̃_t + ε_ψK̃_{t+1}`.
* `natural_output_iff` (the `Ŷⁿ` formula of p. 373), `eq327`, `eq329`, `eq330`, `eq331`,
  `eq331_printed`; `natRate_affine`: `r̂ⁿ = r̂ⁿᶜᶜ + η_r K̂` with `η_r = η_λ(1 − η_k)`.
* `eliminate`, `eq332_iff`: (3.32) `E_t z_{t+1} = A z_t + a r̃_t` with explicit `A`, `a`, valid
  exactly when `a₀ = βε_ψ + c'ρ_yk ≠ 0` (`detM_eq`; the book leaves this unstated);
  `not_form332`: when `a₀ = 0` no `A`, `a` work.
* `eq334`, `eq335`: with `ī = ī^cc + η_r K̂` the interest-rate gap involves only gap variables.
* `Fwd.determinate_iff` (from `ForwardSystems.expSysDeterminate_iff`, with
  `ForwardSystems.pow_entry_bound`, `fsolves_unique`, `fwdVec_spec` restated from the Galí
  Chapter 6 project): a purely forward-looking `n`-dimensional system
  `E_t x_{t+1} = A x_t + w_t` is determinate iff all eigenvalues of `A` lie outside the unit
  circle.
* `eq336_iff`, `econ_determinate_iff`, `determinacy_336`: the model's system (3.36) (explicit
  `Â`, `â`) and the book's determinacy criterion; `eq337_339`: the forward solutions
  (3.37)–(3.39) with explicit `ψ_j = (Â⁻¹)ʲ(−Â⁻¹â)`.
* p. 378: `tracking_stabilises` (zero forcing gives `π_t = π̄`), `const_forcing` (constant
  forcing gives constant inflation); `tracking_intercept`, `printed_intercept_misses` (survey
  error 9: the tracking rule has `ī^cc = r̂ⁿᶜᶜ + π̄`, not `r̂ⁿᶜᶜ`).
* `steady_rate_gap`, `deviation_forcing`: in a steady state with `π̄ ≠ 0` the real-rate gap is
  `−η_λĪ/k`, nonzero unless `η_λ = 0`, so the forcing of (3.36) in deviations is
  `r̂ⁿ − ī + π̄ + r̃̄` rather than the printed `r̂ⁿ − ī + π̄`; `deviation_332`, `deviation_317`
  (fn. 38).
-/

namespace Woodford.PolicyResponseDynamics.InvestmentNaturalRate

open Filter Topology ISBlock ForwardSystems

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The natural rates and Proposition 5.2 -/

/-- Woodford (2003), p. 373: the flexible-price ("natural") values given the actual capital stock
are affine in it: `λ̂ⁿ_t = λ̂ⁿᶜᶜ_t + η_λ K̂_t`, `Ŷⁿ_t = Ŷⁿᶜᶜ_t + η_y K̂_t`,
`K̂ⁿ_{t+1} = K̂ⁿᶜᶜ_{t+1} + η_k K̂_t` (the explicit hypothesis behind Proposition 5.2). -/
def NaturalAffine (ηl ηy ηk : ℝ) (lamn Yn Kn lamcc Ycc Kcc K : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lamn t = lamcc t + ηl • K t ∧ Yn t = Ycc t + ηy • K t ∧
    Kn (t + 1) = Kcc (t + 1) + ηk • K t

/-- Woodford (2003), App. D.3, p. 691: condition (3.7) in the flexible-price equilibrium that
begins at date `t` from the actual capital stock `K̂_t`. Its date-`t+1` variables are the
affine functions of its own capital `K̂ⁿ_{t+1}`, e.g. output `Ŷⁿᶜᶜ_{t+1} + η_y K̂ⁿ_{t+1}`. -/
def FlexEuler (P : Par) (ηl ηy ηk : ℝ) (lamn Kn lamcc Ycc Kcc K u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lamn t + P.eps • (Kn (t + 1) - K t) =
    (P.β * (1 - P.δ)) • 𝔼.E t (lamcc (t + 1) + ηl • Kn (t + 1)) +
      P.cp • (P.ρy • 𝔼.E t (Ycc (t + 1) + ηy • Kn (t + 1)) - P.ρk • Kn (t + 1)) +
      (P.β * P.eps) • (𝔼.E t (Kcc (t + 2) + ηk • Kn (t + 1)) - Kn (t + 1)) + u t

omit 𝔼 in
/-- Woodford (2003), App. D.3, p. 691: "the conditional expectation at `t` of period `t+1`
output in a flexible-price equilibrium … is actually equal to `E_t Ŷⁿ_{t+1} − η_y K̃_{t+1}`": the
flexible-price date-`t+1` value `Xⁿᶜᶜ_{t+1} + η K̂ⁿ_{t+1}` equals `Xⁿ_{t+1} − η K̃_{t+1}`. -/
theorem flex_value {η : ℝ} {Xn Xcc Kn K : ℕ → Ω → ℝ} (t : ℕ)
    (hX : Xn (t + 1) = Xcc (t + 1) + η • K (t + 1)) :
    Xcc (t + 1) + η • Kn (t + 1) = Xn (t + 1) - η • (K (t + 1) - Kn (t + 1)) := by
  rw [hX, smul_sub]; abel

/-- Woodford (2003), App. D.3, p. 691: with the gap `K̃_{t+1}` known at `t`, the flexible-price
expectation is `E_t Xⁿ_{t+1} − η K̃_{t+1}`. -/
theorem flex_expectation {η : ℝ} {Xn Xcc Kn K : ℕ → Ω → ℝ} (t : ℕ)
    (hX : Xn (t + 1) = Xcc (t + 1) + η • K (t + 1))
    (hK : 𝔼.E t (K (t + 1) - Kn (t + 1)) = K (t + 1) - Kn (t + 1)) :
    𝔼.E t (Xcc (t + 1) + η • Kn (t + 1)) =
      𝔼.E t (Xn (t + 1)) - η • (K (t + 1) - Kn (t + 1)) := by
  rw [flex_value t hX, map_sub, map_smul, hK]

/-- Woodford (2003), Proposition 5.2, eq. (3.28)/(D.7), pp. 374 and 691, as corrected (survey
error 2): the gap form of (3.7),
`λ̃_t + ε_ψ K̃_{t+1} = β(1−δ) E_t(λ̃_{t+1} + η_λ K̃_{t+1})
  + c'[ρ_y E_t(Ỹ_{t+1} + η_y K̃_{t+1}) − ρ_k K̃_{t+1}]
  + β ε_ψ [E_t(K̃_{t+2} + η_k K̃_{t+1}) − K̃_{t+1}]`,
for gap processes `λ̃`, `Ỹ` and `K̃` (the latter indexed so that `K̃ (t+1) = K̃_{t+1}`). -/
def GapEuler (P : Par) (ηl ηy ηk : ℝ) (lamt Yt Kt : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lamt t + P.eps • Kt (t + 1) =
    (P.β * (1 - P.δ)) • 𝔼.E t (lamt (t + 1) + ηl • Kt (t + 1)) +
      P.cp • (P.ρy • 𝔼.E t (Yt (t + 1) + ηy • Kt (t + 1)) - P.ρk • Kt (t + 1)) +
      (P.β * P.eps) • (𝔼.E t (Kt (t + 2) + ηk • Kt (t + 1)) - Kt (t + 1))

/-- **Woodford (2003), Proposition 5.2**, pp. 374 and 691, in corrected form: given the affine
representation of the natural values and condition (3.7) in the flexible-price equilibrium
beginning from the actual capital stock, the sticky-price (3.7) holds if and only if the gaps
`λ̃ = λ̂ − λ̂ⁿ`, `Ỹ = Ŷ − Ŷⁿ`, `K̃_{t+1} = K̂_{t+1} − K̂ⁿ_{t+1}` satisfy the corrected (3.28). (The
disturbance `u_t` is common to both and cancels; no information assumption is needed.) -/
theorem prop52 {P : Par} {ηl ηy ηk : ℝ} {lam Y K u lamn Yn Kn lamcc Ycc Kcc : ℕ → Ω → ℝ}
    (hA : NaturalAffine ηl ηy ηk lamn Yn Kn lamcc Ycc Kcc K)
    (hflex : FlexEuler 𝔼 P ηl ηy ηk lamn Kn lamcc Ycc Kcc K u) :
    CapitalEuler 𝔼 P lam Y K u ↔
      GapEuler 𝔼 P ηl ηy ηk (fun t => lam t - lamn t) (fun t => Y t - Yn t)
        (fun t => K t - Kn t) := by
  refine forall_congr' fun t => ?_
  have hf := hflex t
  obtain ⟨hl1, hy1, hk2⟩ := hA (t + 1)
  have hk' : Kcc (t + 2) + ηk • Kn (t + 1) = Kn (t + 2) - ηk • (K (t + 1) - Kn (t + 1)) := by
    rw [show t + 2 = t + 1 + 1 from rfl, hk2, smul_sub]; abel
  rw [flex_value t hl1, flex_value t hy1, hk'] at hf
  simp only [map_add, map_sub, map_smul] at hf ⊢
  constructor
  · intro h
    funext ω
    have h1 := congrFun h ω
    have h2 := congrFun hf ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination h1 - h2
  · intro h
    funext ω
    have h1 := congrFun h ω
    have h2 := congrFun hf ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linear_combination h1 + h2

/-- Woodford (2003), eq. (3.28), p. 374, as printed: the expression
`c'[ρ_y(E_t Ỹ_{t+1} + η_y K̃_{t+1}) − ρ_k K̃_{t+1}]
  + β ε_ψ[(E_t K̃_{t+2} + η_k K̃_{t+1}) − K̃_{t+1}]` (no left-hand side and no `λ̃` terms). -/
def printed328 (P : Par) (ηy ηk : ℝ) (Yt Kt : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  P.cp • (P.ρy • (𝔼.E t (Yt (t + 1)) + ηy • Kt (t + 1)) - P.ρk • Kt (t + 1)) +
    (P.β * P.eps) • ((𝔼.E t (Kt (t + 2)) + ηk • Kt (t + 1)) - Kt (t + 1))

/-- Woodford (2003), (3.28)/(D.7) (survey error 2), counterexample: under perfect foresight the
gaps `λ̃ ≡ ρ_y`, `Ỹ ≡ 1`, `K̃ ≡ 0` satisfy the corrected (3.28), yet the printed expression
equals `c'ρ_y ≠ 0` (so it is not zero), and it differs from `λ̃_t + ε_ψ K̃_{t+1} = ρ_y` (so the
reading "LHS = printed expression" fails too), whenever `c' ≠ 0`, `ρ_y ≠ 0`, `β(1−δ) ≠ 0`. -/
theorem printed328_false (P : Par) (ηl ηy ηk : ℝ) (hcp : P.cp ≠ 0) (hρ : P.ρy ≠ 0)
    (hb : P.β * (1 - P.δ) ≠ 0) :
    GapEuler perfectForesight P ηl ηy ηk (fun _ _ => P.ρy) (fun _ _ => 1) (fun _ _ => 0) ∧
      printed328 perfectForesight P ηy ηk (fun _ _ => 1) (fun _ _ => 0) 0 () ≠ 0 ∧
      P.ρy + P.eps * 0 ≠
        printed328 perfectForesight P ηy ηk (fun _ _ => 1) (fun _ _ => 0) 0 () := by
  have hval : printed328 perfectForesight P ηy ηk (fun _ _ => 1) (fun _ _ => 0) 0 () =
      P.cp * P.ρy := by
    simp only [printed328]
    change P.cp * (P.ρy * (1 + ηy * 0) - P.ρk * 0) + P.β * P.eps * ((0 + ηk * 0) - 0) = _
    ring
  refine ⟨fun t => ?_, ?_, ?_⟩
  · funext u
    change P.ρy + P.eps * 0 = P.β * (1 - P.δ) * (P.ρy + ηl * 0) +
      P.cp * (P.ρy * (1 + ηy * 0) - P.ρk * 0) + P.β * P.eps * ((0 + ηk * 0) - 0)
    simp only [Par.cp]; ring
  · rw [hval]; exact mul_ne_zero hcp hρ
  · rw [hval]
    intro h
    apply hb
    have : P.ρy * (1 - P.cp) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hρ
    · simp only [Par.cp] at h'; linarith

/-! ### (3.27), the natural rate of output, and (3.29)–(3.31) -/

/-- Woodford (2003), eq. (3.18), p. 360:
`ŝ_t = (ω + σ⁻¹)Ŷ_t − σ⁻¹Î_t − (ω − ν)K̂_t − [σ⁻¹g_t + ω q_t]`. -/
def MCEq (σ ω ν : ℝ) (s Y I K g q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, s t = (ω + σ⁻¹) • Y t - σ⁻¹ • I t - (ω - ν) • K t - (σ⁻¹ • g t + ω • q t)

/-- Woodford (2003), p. 373: with flexible prices real marginal cost is constant (`ŝ = 0`), so
the natural rate of output solves (3.18) with `ŝ = 0`:
`Ŷⁿ_t = (ω−ν)/(ω+σ⁻¹) K̂_t + σ⁻¹/(ω+σ⁻¹) Îⁿ_t + σ⁻¹/(ω+σ⁻¹) g_t + ω/(ω+σ⁻¹) q_t`
(`InvestmentModel.Linear.natural_output`, date by date). -/
theorem natural_output_iff {σ ω ν : ℝ} (hd : ω + σ⁻¹ ≠ 0) {Yn In K g q : ℕ → Ω → ℝ} :
    MCEq σ ω ν 0 Yn In K g q ↔ ∀ t, Yn t = ((ω - ν) / (ω + σ⁻¹)) • K t +
      (σ⁻¹ / (ω + σ⁻¹)) • In t + (σ⁻¹ / (ω + σ⁻¹)) • g t + (ω / (ω + σ⁻¹)) • q t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun x => ?_
  simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact InvestmentModel.Linear.natural_output hd

/-- Woodford (2003), eq. (3.27), p. 374: subtracting the flexible-price (3.18) (with `ŝ = 0`)
from (3.18) gives `ŝ_t = (ω + σ⁻¹)Ỹ_t − σ⁻¹Ĩ_t` (`InvestmentModel.Linear.eq_3_27`, date by date). -/
theorem eq327 {σ ω ν : ℝ} {s Y I Yn In K g q : ℕ → Ω → ℝ} (h : MCEq σ ω ν s Y I K g q)
    (hn : MCEq σ ω ν 0 Yn In K g q) (t : ℕ) :
    s t = (ω + σ⁻¹) • (Y t - Yn t) - σ⁻¹ • (I t - In t) := by
  funext x
  have e1 := congrFun (h t) x
  have e2 := congrFun (hn t) x
  simp only [Pi.zero_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  exact InvestmentModel.Linear.eq_3_27 e1 e2

/-- Woodford (2003), eq. (3.29), p. 374: (3.8) in both equilibria (natural investment chosen
from the actual `K̂_t`) gives `Ĩ_t = k K̃_{t+1}`. -/
theorem eq329 {P : Par} {I In K Kn : ℕ → Ω → ℝ} (h : InvestEq P I K)
    (hn : ∀ t, In t = P.k • (Kn (t + 1) - (1 - P.δ) • K t)) (t : ℕ) :
    I t - In t = P.k • (K (t + 1) - Kn (t + 1)) := by
  rw [h t, hn t, ← smul_sub]; congr 1; abel

/-- Woodford (2003), eq. (3.30), p. 374: (3.9) in both equilibria gives
`λ̃_t = −σ⁻¹(Ỹ_t − Ĩ_t)`. -/
theorem eq330 {P : Par} {lam Y I g lamn Yn In : ℕ → Ω → ℝ} (h : MUEq P lam Y I g)
    (hn : MUEq P lamn Yn In g) (t : ℕ) :
    lam t - lamn t = -P.σ⁻¹ • ((Y t - Yn t) - (I t - In t)) := by
  rw [h t, hn t, ← smul_sub]; congr 1; abel

/-- Woodford (2003), p. 373: the natural real rate given `K̂_t`, from (3.10) in the
flexible-price equilibrium beginning at `t`: `r̂ⁿ_t = λ̂ⁿ_t − E_t(λ̂ⁿᶜᶜ_{t+1} + η_λ K̂ⁿ_{t+1})`. -/
def natRate (ηl : ℝ) (lamn lamcc Kn : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  lamn t - 𝔼.E t (lamcc (t + 1) + ηl • Kn (t + 1))

/-- Woodford (2003), eq. (3.31), p. 374: with `r̂_t = ı̂_t − E_tπ_{t+1} = λ̂_t − E_tλ̂_{t+1}`
(3.10), the real-rate gap is `r̃_t = λ̃_t − E_t(λ̃_{t+1} + η_λ K̃_{t+1})`. -/
theorem eq331 {ηl ηy ηk : ℝ} {lam i π lamn Yn Kn lamcc Ycc Kcc K : ℕ → Ω → ℝ}
    (hF : FisherEq 𝔼 lam i π) (hA : NaturalAffine ηl ηy ηk lamn Yn Kn lamcc Ycc Kcc K) (t : ℕ) :
    (i t - 𝔼.E t (π (t + 1))) - natRate 𝔼 ηl lamn lamcc Kn t =
      (lam t - lamn t) - 𝔼.E t ((lam (t + 1) - lamn (t + 1)) +
        ηl • (K (t + 1) - Kn (t + 1))) := by
  rw [natRate, flex_value t (hA (t + 1)).1, hF t]
  simp only [map_add, map_sub, map_smul]
  abel

/-- Woodford (2003), eq. (3.31), p. 374, as printed: when `K̃_{t+1}` is known at `t`,
`r̃_t = λ̃_t − (E_t λ̃_{t+1} + η_λ K̃_{t+1})`. -/
theorem eq331_printed {ηl ηy ηk : ℝ} {lam i π lamn Yn Kn lamcc Ycc Kcc K : ℕ → Ω → ℝ}
    (hF : FisherEq 𝔼 lam i π) (hA : NaturalAffine ηl ηy ηk lamn Yn Kn lamcc Ycc Kcc K) (t : ℕ)
    (hK : 𝔼.E t (K (t + 1) - Kn (t + 1)) = K (t + 1) - Kn (t + 1)) :
    (i t - 𝔼.E t (π (t + 1))) - natRate 𝔼 ηl lamn lamcc Kn t =
      (lam t - lamn t) - (𝔼.E t (lam (t + 1) - lamn (t + 1)) +
        ηl • (K (t + 1) - Kn (t + 1))) := by
  rw [eq331 𝔼 hF hA t, map_add, map_smul, hK]

/-- Woodford (2003), p. 373: the natural rate of interest is affine in the capital stock,
`r̂ⁿ_t = r̂ⁿᶜᶜ_t + η_r K̂_t`, with `η_r = η_λ(1 − η_k)` and the exogenous intercept
`r̂ⁿᶜᶜ_t = λ̂ⁿᶜᶜ_t − E_t(λ̂ⁿᶜᶜ_{t+1} + η_λ K̂ⁿᶜᶜ_{t+1})`, when `K̂_t` is known at `t`. -/
theorem natRate_affine {ηl ηy ηk : ℝ} {lamn Yn Kn lamcc Ycc Kcc K : ℕ → Ω → ℝ}
    (hA : NaturalAffine ηl ηy ηk lamn Yn Kn lamcc Ycc Kcc K) (t : ℕ)
    (hK : 𝔼.E t (K t) = K t) :
    natRate 𝔼 ηl lamn lamcc Kn t =
      (lamcc t - 𝔼.E t (lamcc (t + 1) + ηl • Kcc (t + 1))) + (ηl * (1 - ηk)) • K t := by
  rw [natRate, (hA t).1, (hA t).2.2]
  simp only [map_add, map_smul, hK, smul_add, smul_smul]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The gap IS system (3.32) -/

/-- Woodford (2003), (3.30) and (3.29): `λ̃_t = −σ⁻¹(Ỹ_t − Ĩ_t)` in terms of `z = (Ỹ, Ĩ)`. -/
noncomputable def lamOf (P : Par) (y j : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := -P.σ⁻¹ • (y t - j t)

/-- Woodford (2003), eq. (3.31) after eliminating `λ̃` and `K̃_{t+1} = Ĩ_t/k`:
`r̃_t = λ̃_t − E_t(λ̃_{t+1} + η_λ Ĩ_t/k)`. -/
def G1 (P : Par) (ηl : ℝ) (y j r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, r t = lamOf P y j t - 𝔼.E t (lamOf P y j (t + 1) + ηl • P.k⁻¹ • j t)

/-- Woodford (2003), corrected (3.28) after eliminating `λ̃` and `K̃_{t+1} = Ĩ_t/k`. -/
def G2 (P : Par) (ηl ηy ηk : ℝ) (y j : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lamOf P y j t + P.eps • P.k⁻¹ • j t =
    (P.β * (1 - P.δ)) • 𝔼.E t (lamOf P y j (t + 1) + ηl • P.k⁻¹ • j t) +
      P.cp • (P.ρy • 𝔼.E t (y (t + 1) + ηy • P.k⁻¹ • j t) - P.ρk • P.k⁻¹ • j t) +
      (P.β * P.eps) • (𝔼.E t (P.k⁻¹ • j (t + 1) + ηk • P.k⁻¹ • j t) - P.k⁻¹ • j t)

/-- Woodford (2003), p. 374: "Using equations (3.29) and (3.30) to eliminate `λ̃_t` and
`K̃_{t+1}` from (3.28) and (3.31)": with `Ĩ_t = k K̃_{t+1}` (`k ≠ 0`) and
`λ̃ = −σ⁻¹(Ỹ − Ĩ)`, the corrected (3.28) is `G2` and (3.31) is `G1`. -/
theorem eliminate {P : Par} (hk : P.k ≠ 0) {ηl ηy ηk : ℝ} {lamt y j Kt r : ℕ → Ω → ℝ}
    (h329 : ∀ t, j t = P.k • Kt (t + 1)) (h330 : ∀ t, lamt t = lamOf P y j t) :
    (GapEuler 𝔼 P ηl ηy ηk lamt y Kt ↔ G2 𝔼 P ηl ηy ηk y j) ∧
      ((∀ t, r t = lamt t - 𝔼.E t (lamt (t + 1) + ηl • Kt (t + 1))) ↔ G1 𝔼 P ηl y j r) := by
  have hK : ∀ t, Kt (t + 1) = P.k⁻¹ • j t := fun t => by
    rw [h329 t, smul_smul, inv_mul_cancel₀ hk, one_smul]
  constructor
  · refine forall_congr' fun t => ?_
    rw [h330 t, h330 (t + 1), hK t, show t + 2 = t + 1 + 1 from rfl, hK (t + 1)]
  · refine forall_congr' fun t => ?_
    rw [h330 t, h330 (t + 1), hK t]

/-- Woodford (2003), (3.32): the coefficient `b(1 − δ)`-weighted combination
`x = c'ρ_y − β(1−δ)σ⁻¹` of `E_t Ỹ_{t+1}` in the second row. -/
noncomputable def cx (P : Par) : ℝ := P.cp * P.ρy - P.β * (1 - P.δ) * P.σ⁻¹

/-- Woodford (2003), (3.32): the coefficient `β(1−δ)σ⁻¹ + βε_ψ/k` of `E_t Ĩ_{t+1}` in the
second row. -/
noncomputable def cy (P : Par) : ℝ := P.β * (1 - P.δ) * P.σ⁻¹ + P.β * P.eps * P.k⁻¹

/-- Woodford (2003), (3.32): the coefficient of `Ĩ_t` in the first row, `η_λ/k − σ⁻¹`. -/
noncomputable def c1 (P : Par) (ηl : ℝ) : ℝ := ηl * P.k⁻¹ - P.σ⁻¹

/-- Woodford (2003), (3.32): the coefficient of `Ĩ_t` in the second row,
`σ⁻¹ + [ε_ψ(1+β) − β(1−δ)η_λ − c'ρ_yη_y + c'ρ_k − βε_ψη_k]/k`. -/
noncomputable def c2 (P : Par) (ηl ηy ηk : ℝ) : ℝ :=
  P.σ⁻¹ + P.k⁻¹ * (P.eps * (1 + P.β) - P.β * (1 - P.δ) * ηl - P.cp * P.ρy * ηy + P.cp * P.ρk -
    P.β * P.eps * ηk)

/-- Woodford (2003), (3.32): the determinant `σ⁻¹(x + y) = σ⁻¹ a₀/k` of the system. -/
noncomputable def detM (P : Par) : ℝ := P.σ⁻¹ * (cx P + cy P)

/-- Woodford (2003), (3.32): `det = σ⁻¹ a₀ / k`, so the system can be solved for
`E_t z_{t+1}` exactly when `a₀ = βε_ψ + c'ρ_y k ≠ 0` (given `σ, k ≠ 0`). -/
theorem detM_eq (P : Par) (hk : P.k ≠ 0) : detM P = P.σ⁻¹ * P.a0 / P.k := by
  simp only [detM, cx, cy, Par.a0]
  field_simp
  ring

/-- Woodford (2003), (3.32): the matrix `A`. -/
noncomputable def Amat (P : Par) (ηl ηy ηk : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![P.σ⁻¹ * (cy P - P.σ⁻¹) / detM P, (cy P * c1 P ηl + P.σ⁻¹ * c2 P ηl ηy ηk) / detM P;
    -(P.σ⁻¹ * (cx P + P.σ⁻¹)) / detM P, (-(cx P * c1 P ηl) + P.σ⁻¹ * c2 P ηl ηy ηk) / detM P]

/-- Woodford (2003), (3.32): the vector `a`. -/
noncomputable def avec (P : Par) : Fin 2 → ℝ := ![cy P / detM P, -cx P / detM P]

omit 𝔼 in
/-- Woodford (2003), (3.32) (the 2×2 elimination): for `D = s(x + y) ≠ 0`,
`s e₁ − s e₂ = R₁ ∧ x e₁ + y e₂ = R₂ ↔ e₁ = (yR₁ + sR₂)/D ∧ e₂ = (−xR₁ + sR₂)/D`. -/
theorem solve2 {s x y e1 e2 R1 R2 : ℝ} (hD : s * (x + y) ≠ 0) :
    (s * e1 - s * e2 = R1 ∧ x * e1 + y * e2 = R2) ↔
      (e1 = (y * R1 + s * R2) / (s * (x + y)) ∧ e2 = (-(x * R1) + s * R2) / (s * (x + y))) := by
  rw [eq_div_iff hD, eq_div_iff hD]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination y * h1 + s * h2, by linear_combination (-x) * h1 + s * h2⟩
  · rintro ⟨h1, h2⟩
    constructor
    · refine mul_left_cancel₀ hD ?_
      linear_combination s * h1 - s * h2
    · refine mul_left_cancel₀ hD ?_
      linear_combination x * h1 + y * h2

/-- Woodford (2003), eq. (3.32), p. 374, in full: for `σ, k ≠ 0`, `a₀ ≠ 0` (the invertibility
condition the book leaves unstated) and `Ĩ` adapted, the gap equations (3.31) and corrected
(3.28) (after elimination, `G1`, `G2`) hold if and only if
`E_t z_{t+1} = A z_t + a r̃_t`, `z = (Ỹ, Ĩ)`, with the explicit `A = Amat`, `a = avec`. -/
theorem eq332_iff {P : Par} (hσ : P.σ ≠ 0) (hk : P.k ≠ 0) (ha0 : P.a0 ≠ 0) {ηl ηy ηk : ℝ}
    {y j r : ℕ → Ω → ℝ} (hj : 𝔼.Adapted j) :
    (G1 𝔼 P ηl y j r ∧ G2 𝔼 P ηl ηy ηk y j) ↔
      ∀ t, 𝔼.E t (y (t + 1)) = (Amat P ηl ηy ηk 0 0) • y t + (Amat P ηl ηy ηk 0 1) • j t +
          (avec P 0) • r t ∧
        𝔼.E t (j (t + 1)) = (Amat P ηl ηy ηk 1 0) • y t + (Amat P ηl ηy ηk 1 1) • j t +
          (avec P 1) • r t := by
  have hD : P.σ⁻¹ * (cx P + cy P) ≠ 0 := by
    rw [show P.σ⁻¹ * (cx P + cy P) = detM P from rfl, detM_eq P hk]
    exact div_ne_zero (mul_ne_zero (inv_ne_zero hσ) ha0) hk
  rw [show (G1 𝔼 P ηl y j r ∧ G2 𝔼 P ηl ηy ηk y j) ↔ ∀ t, (_ ∧ _) from forall_and.symm]
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff, funext_iff, funext_iff, ← forall_and, ← forall_and]
  refine forall_congr' fun x => ?_
  have e := solve2 (e1 := 𝔼.E t (y (t + 1)) x) (e2 := 𝔼.E t (j (t + 1)) x)
    (R1 := r t x + P.σ⁻¹ * y t x + c1 P ηl * j t x)
    (R2 := -(P.σ⁻¹ * y t x) + c2 P ηl ηy ηk * j t x) hD
  have hjx : 𝔼.E t (j t) x = j t x := by rw [hj t]
  simp only [lamOf, map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, hjx]
  simp only [Amat, avec, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [show detM P = P.σ⁻¹ * (cx P + cy P) from rfl]
  constructor
  · rintro ⟨g1, g2⟩
    have h1 : P.σ⁻¹ * 𝔼.E t (y (t + 1)) x - P.σ⁻¹ * 𝔼.E t (j (t + 1)) x =
        r t x + P.σ⁻¹ * y t x + c1 P ηl * j t x := by
      simp only [c1]; linear_combination -g1
    have h2 : cx P * 𝔼.E t (y (t + 1)) x + cy P * 𝔼.E t (j (t + 1)) x =
        -(P.σ⁻¹ * y t x) + c2 P ηl ηy ηk * j t x := by
      simp only [cx, cy, c2]; linear_combination -g2
    obtain ⟨q1, q2⟩ := e.mp ⟨h1, h2⟩
    constructor
    · rw [q1]; ring
    · rw [q2]; ring
  · rintro ⟨q1, q2⟩
    obtain ⟨h1, h2⟩ := e.mpr ⟨by rw [q1]; ring, by rw [q2]; ring⟩
    constructor
    · simp only [c1] at h1; linear_combination -h1
    · simp only [cx, cy, c2] at h2; linear_combination -h2

/-- Woodford (2003), p. 374: a path of `z_{t+1} = A z_t + a r̃_t` with `r̃ = 0` from `z_0 = (1, 0)`
(used to show that `a₀ ≠ 0` is needed for (3.32)). -/
def zseq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | t + 1 => (A 0 0 * (zseq A t).1 + A 0 1 * (zseq A t).2,
      A 1 0 * (zseq A t).1 + A 1 1 * (zseq A t).2)

/-- Woodford (2003), (3.32), p. 374: the invertibility condition is necessary. If
`a₀ = βε_ψ + c'ρ_y k = 0` (with `σ > 0`, `k ≠ 0`, `c' > 0`, `ρ_y > 0`), the gap equations cannot
be written as `E_t z_{t+1} = A z_t + a r̃_t` for any `A`, `a`: the perfect-foresight path of the
latter with `r̃ = 0` and `z_0 = (1, 0)` violates `G1 ∧ G2` at `t = 0`, since those two equations
would then force `c'(ρ_y + σ⁻¹) = 0`. -/
theorem not_form332 (P : Par) (hσ : 0 < P.σ) (hk : P.k ≠ 0) (hcp : 0 < P.cp) (hρy : 0 < P.ρy)
    (ha0 : P.a0 = 0) (ηl ηy ηk : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) :
    ∃ y j r : ℕ → Unit → ℝ,
      (∀ t, perfectForesight.E t (y (t + 1)) = A 0 0 • y t + A 0 1 • j t + a 0 • r t ∧
        perfectForesight.E t (j (t + 1)) = A 1 0 • y t + A 1 1 • j t + a 1 • r t) ∧
      ¬ (G1 perfectForesight P ηl y j r ∧ G2 perfectForesight P ηl ηy ηk y j) := by
  refine ⟨fun t _ => (zseq A t).1, fun t _ => (zseq A t).2, fun _ _ => 0, fun t => ?_, ?_⟩
  · constructor
    · funext u
      change (zseq A (t + 1)).1 = A 0 0 * (zseq A t).1 + A 0 1 * (zseq A t).2 + a 0 * 0
      simp [zseq]
    · funext u
      change (zseq A (t + 1)).2 = A 1 0 * (zseq A t).1 + A 1 1 * (zseq A t).2 + a 1 * 0
      simp [zseq]
  · rintro ⟨g1, g2⟩
    have e1 := congrFun (g1 0) ()
    have e2 := congrFun (g2 0) ()
    change (0 : ℝ) = -P.σ⁻¹ * ((zseq A 0).1 - (zseq A 0).2) -
      (-P.σ⁻¹ * ((zseq A 1).1 - (zseq A 1).2) + ηl * (P.k⁻¹ * (zseq A 0).2)) at e1
    change -P.σ⁻¹ * ((zseq A 0).1 - (zseq A 0).2) + P.eps * (P.k⁻¹ * (zseq A 0).2) =
      P.β * (1 - P.δ) * (-P.σ⁻¹ * ((zseq A 1).1 - (zseq A 1).2) + ηl * (P.k⁻¹ * (zseq A 0).2)) +
      P.cp * (P.ρy * ((zseq A 1).1 + ηy * (P.k⁻¹ * (zseq A 0).2)) - P.ρk * (P.k⁻¹ * (zseq A 0).2))
      + P.β * P.eps * (P.k⁻¹ * (zseq A 1).2 + ηk * (P.k⁻¹ * (zseq A 0).2) -
        P.k⁻¹ * (zseq A 0).2) at e2
    set y1 := (zseq A 1).1
    set j1 := (zseq A 1).2
    have hz0 : zseq A 0 = (1, 0) := rfl
    simp only [hz0] at e1 e2
    have hs : P.σ⁻¹ ≠ 0 := inv_ne_zero hσ.ne'
    have hD1 : y1 - j1 = 1 := by
      have : P.σ⁻¹ * (y1 - j1 - 1) = 0 := by linear_combination -e1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hs
      · linarith
    have hb : P.β * P.eps * P.k⁻¹ + P.cp * P.ρy = 0 := by
      simp only [Par.a0] at ha0
      field_simp
      linear_combination ha0
    have key : P.cp * (P.ρy + P.σ⁻¹) = 0 := by
      simp only [Par.cp] at hb e2 ⊢
      linear_combination -e2 - j1 * hb - ((1 - P.β * (1 - P.δ)) * P.ρy -
        P.β * (1 - P.δ) * P.σ⁻¹) * hD1
    have : 0 < P.cp * (P.ρy + P.σ⁻¹) := mul_pos hcp (by positivity)
    linarith

/-! ### The policy rule (3.33)–(3.35) -/

/-- Woodford (2003), eq. (3.34), p. 375: under the rule (3.33)
`ı̂_t = ī_t + φ_π(π_t − π̄) + φ_x(x_t − x̄)/4`, the interest-rate gap
`r̃_t = (ı̂_t − E_tπ_{t+1}) − r̂ⁿ_t` equals
`ī_t − r̂ⁿ_t − π̄ − E_t(π_{t+1} − π̄) + φ_π(π_t − π̄) + φ_x(x_t − x̄)/4`. -/
theorem eq334 {πbar xbar φπ φx : ℝ} {i ibar π x rn : ℕ → Ω → ℝ}
    (hrule : ∀ t, i t = ibar t + φπ • (π t - fun _ => πbar) + (φx / 4) • (x t - fun _ => xbar))
    (t : ℕ) :
    (i t - 𝔼.E t (π (t + 1))) - rn t = ibar t - rn t - (fun _ => πbar) -
      𝔼.E t (π (t + 1) - fun _ => πbar) + φπ • (π t - fun _ => πbar) +
        (φx / 4) • (x t - fun _ => xbar) := by
  rw [hrule t, map_sub, 𝔼.const]
  abel

/-- Woodford (2003), eq. (3.35), p. 375: if `ī_t = ī^cc_t + η_r K̂_t` and
`r̂ⁿ_t = r̂ⁿᶜᶜ_t + η_r K̂_t` (`natRate_affine`, `η_r = η_λ(1 − η_k)`), then
`r̃_t = ī^cc_t − r̂ⁿᶜᶜ_t − π̄ − E_t(π_{t+1} − π̄) + φ_π(π_t − π̄) + φ_x(x_t − x̄)/4`: the capital
stock drops out and only gap variables and exogenous terms remain. -/
theorem eq335 {πbar xbar φπ φx ηr : ℝ} {i ibar ibarcc π x rn rncc K : ℕ → Ω → ℝ}
    (hrule : ∀ t, i t = ibar t + φπ • (π t - fun _ => πbar) + (φx / 4) • (x t - fun _ => xbar))
    (hib : ∀ t, ibar t = ibarcc t + ηr • K t) (hrn : ∀ t, rn t = rncc t + ηr • K t) (t : ℕ) :
    (i t - 𝔼.E t (π (t + 1))) - rn t = ibarcc t - rncc t - (fun _ => πbar) -
      𝔼.E t (π (t + 1) - fun _ => πbar) + φπ • (π t - fun _ => πbar) +
        (φx / 4) • (x t - fun _ => xbar) := by
  rw [eq334 𝔼 hrule t, hib t, hrn t]
  abel

/-- Woodford (2003), p. 378 (survey error 9): the tracking rule `ī_t = r̂ⁿ_t + π̄` is of the form
(3.35) with intercept `ī^cc_t = r̂ⁿᶜᶜ_t + π̄`, not `r̂ⁿᶜᶜ_t` as printed. -/
theorem tracking_intercept {πbar ηr : ℝ} {ibar rn rncc K : ℕ → Ω → ℝ}
    (htrack : ∀ t, ibar t = rn t + fun _ => πbar) (hrn : ∀ t, rn t = rncc t + ηr • K t)
    (t : ℕ) : ibar t = (rncc t + fun _ => πbar) + ηr • K t := by
  rw [htrack t, hrn t]; abel

/-- Woodford (2003), p. 378 (survey error 9): with the printed intercept `ī^cc_t = r̂ⁿᶜᶜ_t`, the
rule (3.35) misses the tracking target `ī_t = r̂ⁿ_t + π̄` whenever `π̄ ≠ 0`. -/
theorem printed_intercept_misses [Nonempty Ω] {πbar ηr : ℝ} {ibar rn rncc K : ℕ → Ω → ℝ}
    (hib : ∀ t, ibar t = rncc t + ηr • K t) (hrn : ∀ t, rn t = rncc t + ηr • K t)
    (hπ : πbar ≠ 0) (t : ℕ) : ibar t ≠ rn t + fun _ => πbar := by
  intro h
  rw [hib t, hrn t] at h
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun h ω
  simp only [Pi.add_apply] at this
  exact hπ (by linarith)

/-! ### Purely forward-looking `n`-dimensional systems (for (3.36))

The general theory (`ExpSys`, `EigenOut`, `existsUnique_of_eigenOut`, `expSysDeterminate_iff`)
is in `ForwardSystems`. -/

namespace Fwd

/-- **Woodford (2003), p. 376** (the determinacy criterion for (3.36), proved for any purely
forward-looking `n`-dimensional system, `ForwardSystems.expSysDeterminate_iff`):
`E_t x_{t+1} = A x_t + w_t` has a unique bounded solution for every bounded adapted forcing if
and only if all eigenvalues of `A` lie outside the unit circle. -/
theorem determinate_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) [Nonempty Ω] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ExpSysDeterminate 𝔼 A ↔ EigenOut A :=
  expSysDeterminate_iff 𝔼 A

end Fwd

/-! ### The complete system (3.36) and its determinacy -/

/-- Woodford (2003), eq. (3.36), pp. 375–376: the coefficients of the gap system — the
(3.32) matrix `A` and vector `a`, the (3.27) weights `ŝ = m_Y Ỹ − m_I Ĩ` (`m_Y = ω + σ⁻¹`,
`m_I = σ⁻¹`), the (3.17) coefficients `ξ₀, ξ₁, ψ₁, ψ₂` and the rule coefficients `φ_π, φ_x`. -/
structure Sys36 where
  A00 : ℝ
  A01 : ℝ
  A10 : ℝ
  A11 : ℝ
  a0 : ℝ
  a1 : ℝ
  mY : ℝ
  mI : ℝ
  ξ0 : ℝ
  ξ1 : ℝ
  ψ1 : ℝ
  ψ2 : ℝ
  φπ : ℝ
  φx : ℝ

namespace Sys36

open scoped Matrix

/-- Woodford (2003), (3.36), p. 376: first row of `Â` ((3.32) with (3.34) substituted). -/
noncomputable def row0 (S : Sys36) : Fin 4 → ℝ :=
  ![S.A00 + S.a0 * (S.φx / 4), S.A01, -S.a0, S.a0 * S.φπ]

/-- Woodford (2003), (3.36), p. 376: second row of `Â`. -/
noncomputable def row1 (S : Sys36) : Fin 4 → ℝ :=
  ![S.A10 + S.a1 * (S.φx / 4), S.A11, -S.a1, S.a1 * S.φπ]

/-- Woodford (2003), (3.36), p. 376: third row of `Â` ((3.17) solved for `E_t π_{t+2}`, with
(3.27) and the first two rows substituted). -/
noncomputable def row2 (S : Sys36) : Fin 4 → ℝ := fun j =>
  (S.ξ0 * (![S.mY, -S.mI, 0, 0] : Fin 4 → ℝ) j - S.ξ1 * (S.mY * S.row0 j - S.mI * S.row1 j) +
    (![0, 0, S.ψ1, -1] : Fin 4 → ℝ) j) / S.ψ2

/-- Woodford (2003), (3.36), p. 376: the matrix `Â` for `ẑ = (Ỹ − x̄, Ĩ − Ī, E_tπ_{t+1} − π̄,
π_t − π̄)`; the fourth row is the identity `E_t ẑ₄_{t+1} = ẑ₃_t`. -/
noncomputable def Ahat (S : Sys36) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![S.row0, S.row1, S.row2, ![0, 0, 1, 0]]

/-- Woodford (2003), (3.36), p. 376: the vector `â` multiplying the forcing. -/
noncomputable def ahat (S : Sys36) : Fin 4 → ℝ :=
  ![-S.a0, -S.a1, -(S.ξ1 * (S.mY * -S.a0 - S.mI * -S.a1)) / S.ψ2, 0]

end Sys36

/-- Woodford (2003), (3.27): real marginal cost `ŝ_t = m_Y X_t − m_I J_t` (deviations). -/
def S36 (S : Sys36) (X J : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := S.mY • X t - S.mI • J t

/-- Woodford (2003), (3.34) in deviations: `r̃_t = −f_t − E_tΠ_{t+1} + φ_πΠ_t + φ_x X_t/4`. -/
noncomputable def R36 (S : Sys36) (f X Pv : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  -f t - 𝔼.E t (Pv (t + 1)) + S.φπ • Pv t + (S.φx / 4) • X t

/-- Woodford (2003), p. 375: the equilibrium conditions (3.17), (3.27), (3.32), (3.34) for the
deviations `X = Ỹ − x̄`, `J = Ĩ − Ī`, `Π = π − π̄`, with forcing `f`. -/
def EconEq (S : Sys36) (f X J Pv : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (X (t + 1)) = S.A00 • X t + S.A01 • J t + S.a0 • R36 𝔼 S f X Pv t ∧
    𝔼.E t (J (t + 1)) = S.A10 • X t + S.A11 • J t + S.a1 • R36 𝔼 S f X Pv t ∧
    Pv t = S.ξ0 • S36 S X J t - S.ξ1 • 𝔼.E t (S36 S X J (t + 1)) + S.ψ1 • 𝔼.E t (Pv (t + 1)) -
      S.ψ2 • 𝔼.E t (Pv (t + 2))

/-- Woodford (2003), p. 376: the stacked vector `ẑ_t = (X_t, J_t, E_tΠ_{t+1}, Π_t)`. -/
def zvec (X J Pv : ℕ → Ω → ℝ) (t : ℕ) : Fin 4 → Ω → ℝ := ![X t, J t, 𝔼.E t (Pv (t + 1)), Pv t]

/-- Woodford (2003), (3.36): the forcing vector `â f_t`. -/
noncomputable def wvec (S : Sys36) (f : ℕ → Ω → ℝ) (t : ℕ) : Fin 4 → Ω → ℝ :=
  fun i => S.ahat i • f t

/-- **Woodford (2003), eq. (3.36), pp. 375–376**: for adapted `X, J, Π` and `ψ₂ ≠ 0`, the
equilibrium conditions hold if and only if `ẑ_t = (X_t, J_t, E_tΠ_{t+1}, Π_t)` satisfies
`E_t ẑ_{t+1} = Â ẑ_t + â f_t`. -/
theorem eq336_iff {S : Sys36} (hψ2 : S.ψ2 ≠ 0) {f X J Pv : ℕ → Ω → ℝ} :
    EconEq 𝔼 S f X J Pv ↔ ExpSys 𝔼 S.Ahat (wvec S f) (zvec 𝔼 X J Pv) := by
  have hrow : ∀ t ω,
      (∀ i, 𝔼.E t (zvec 𝔼 X J Pv (t + 1) i) ω =
        rvMul S.Ahat (zvec 𝔼 X J Pv t) i ω + wvec S f t i ω) ↔
      (𝔼.E t (X (t + 1)) ω = (S.A00 + S.a0 * (S.φx / 4)) * X t ω + S.A01 * J t ω +
          -S.a0 * 𝔼.E t (Pv (t + 1)) ω + S.a0 * S.φπ * Pv t ω + -S.a0 * f t ω) ∧
        (𝔼.E t (J (t + 1)) ω = (S.A10 + S.a1 * (S.φx / 4)) * X t ω + S.A11 * J t ω +
          -S.a1 * 𝔼.E t (Pv (t + 1)) ω + S.a1 * S.φπ * Pv t ω + -S.a1 * f t ω) ∧
        (𝔼.E t (Pv (t + 2)) ω = S.row2 0 * X t ω + S.row2 1 * J t ω +
          S.row2 2 * 𝔼.E t (Pv (t + 1)) ω + S.row2 3 * Pv t ω + S.ahat 2 * f t ω) := by
    intro t ω
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · have := h 0
        simpa [zvec, wvec, rvMul_apply, Fin.sum_univ_four, Sys36.Ahat, Sys36.row0,
          Sys36.ahat] using this
      · have := h 1
        simpa [zvec, wvec, rvMul_apply, Fin.sum_univ_four, Sys36.Ahat, Sys36.row1,
          Sys36.ahat] using this
      · have := h 2
        simpa [zvec, wvec, rvMul_apply, Fin.sum_univ_four, Sys36.Ahat,
          𝔼.tower (Nat.le_succ t)] using this
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i
      · simpa [zvec, wvec, rvMul_apply, Fin.sum_univ_four, Sys36.Ahat, Sys36.row0,
          Sys36.ahat] using h0
      · simpa [zvec, wvec, rvMul_apply, Fin.sum_univ_four, Sys36.Ahat, Sys36.row1,
          Sys36.ahat] using h1
      · simpa [zvec, wvec, rvMul_apply, Fin.sum_univ_four, Sys36.Ahat,
          𝔼.tower (Nat.le_succ t)] using h2
      · simp [zvec, wvec, rvMul_apply, Fin.sum_univ_four, Sys36.Ahat, Sys36.ahat]
  unfold ExpSys EconEq
  refine forall_congr' fun t => ?_
  have hR : (∀ i, 𝔼.E t (zvec 𝔼 X J Pv (t + 1) i) =
      rvMul S.Ahat (zvec 𝔼 X J Pv t) i + wvec S f t i) ↔
      ∀ ω, ∀ i, 𝔼.E t (zvec 𝔼 X J Pv (t + 1) i) ω =
        rvMul S.Ahat (zvec 𝔼 X J Pv t) i ω + wvec S f t i ω := by
    simp only [funext_iff, Pi.add_apply]; exact forall_comm
  rw [hR, funext_iff, funext_iff, funext_iff, ← forall_and, ← forall_and]
  refine forall_congr' fun ω => ?_
  rw [hrow t ω]
  simp only [R36, S36, map_sub, map_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  simp only [Sys36.row2, Sys36.row0, Sys36.row1, Sys36.ahat, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons]
  constructor
  · rintro ⟨e1, e2, e4⟩
    refine ⟨by linear_combination e1, by linear_combination e2, ?_⟩
    field_simp
    linear_combination 4 * e4 - 4 * S.ξ1 * S.mY * e1 + 4 * S.ξ1 * S.mI * e2
  · rintro ⟨e1, e2, e3⟩
    refine ⟨by linear_combination e1, by linear_combination e2, ?_⟩
    linear_combination (norm := (field_simp; ring)) S.ψ2 * e3 + S.ξ1 * S.mY * e1 -
      S.ξ1 * S.mI * e2

/-- Woodford (2003), p. 376: a bounded adapted equilibrium of (3.17), (3.27), (3.32), (3.34)
(in deviations) for the forcing `f`. -/
def EconSol (S : Sys36) (f X J Pv : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted X ∧ 𝔼.Adapted J ∧ 𝔼.Adapted Pv ∧ BoundedProc X ∧ BoundedProc J ∧ BoundedProc Pv ∧
    EconEq 𝔼 S f X J Pv

/-- Woodford (2003), p. 376: the policy rule (3.33), (3.35) yields determinate equilibrium
dynamics — for every bounded adapted forcing there is exactly one bounded adapted equilibrium
`(Ỹ − x̄, Ĩ − Ī, π − π̄)`. -/
def EconDeterminate (S : Sys36) : Prop :=
  ∀ f : ℕ → Ω → ℝ, BoundedProc f → 𝔼.Adapted f →
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), EconSol 𝔼 S f q.1 q.2.1 q.2.2

/-- Woodford (2003), p. 376: `ẑ` is adapted when `X, J, Π` are. -/
theorem zvec_adapted {X J Pv : ℕ → Ω → ℝ} (hX : 𝔼.Adapted X) (hJ : 𝔼.Adapted J)
    (hP : 𝔼.Adapted Pv) : VAdapted 𝔼 (zvec 𝔼 X J Pv) := fun t i => by
  fin_cases i <;> simp [zvec, hX t, hJ t, hP t, 𝔼.E_E_self]

/-- Woodford (2003), p. 376: `ẑ` is bounded when `X, J, Π` are. -/
theorem zvec_bounded {X J Pv : ℕ → Ω → ℝ} (hX : BoundedProc X) (hJ : BoundedProc J)
    (hP : BoundedProc Pv) : VBounded (zvec 𝔼 X J Pv) := by
  obtain ⟨M1, h1⟩ := hX
  obtain ⟨M2, h2⟩ := hJ
  obtain ⟨M3, h3⟩ := hP
  refine ⟨|M1| + |M2| + |M3|, fun t i ω => ?_⟩
  have a1 := (h1 t ω).trans (le_abs_self M1)
  have a2 := (h2 t ω).trans (le_abs_self M2)
  have a3 := (h3 t ω).trans (le_abs_self M3)
  have a4 := (𝔼.abs_E_le (h3 (t + 1)) t ω).trans (le_abs_self M3)
  have p1 := abs_nonneg M1
  have p2 := abs_nonneg M2
  have p3 := abs_nonneg M3
  fin_cases i <;> simp [zvec] <;> linarith

/-- Woodford (2003), p. 376 ("The fourth row is simply an identity"): every solution of (3.36)
is the stacked vector of its own components, `x_t = (x₁, x₂, E_t x₄_{t+1}, x₄)`. -/
theorem zvec_of_sol {S : Sys36} {f : ℕ → Ω → ℝ} {x : ℕ → Fin 4 → Ω → ℝ}
    (h : ExpSys 𝔼 S.Ahat (wvec S f) x) :
    x = zvec 𝔼 (fun t => x t 0) (fun t => x t 1) (fun t => x t 3) := by
  funext t i
  fin_cases i
  · rfl
  · rfl
  · funext ω
    have := congrFun (h t 3) ω
    simp [rvMul_apply, Fin.sum_univ_four, Sys36.Ahat, wvec, Sys36.ahat] at this
    simp [zvec, this]
  · rfl

/-- Woodford (2003), (3.36): the forcing vector `â f` is bounded and adapted when `f` is. -/
theorem wvec_bounded_adapted {S : Sys36} {f : ℕ → Ω → ℝ} {Mf : ℝ} (hf : ∀ t ω, |f t ω| ≤ Mf)
    (hfa : 𝔼.Adapted f) :
    (∀ t i ω, |wvec S f t i ω| ≤ (∑ i, |S.ahat i|) * max Mf 0) ∧ VAdapted 𝔼 (wvec S f) := by
  refine ⟨fun t i ω => ?_, fun t i => ?_⟩
  · simp only [wvec, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul (Finset.single_le_sum (f := fun i => |S.ahat i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)) ((hf t ω).trans (le_max_left _ _))
      (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  · simp only [wvec, map_smul, hfa t]

/-- **Woodford (2003), p. 376**: "a policy rule of the kind defined by (3.33) and (3.35) results
in determinate equilibrium dynamics … if and only if the matrix `Â` has all four eigenvalues
outside the unit circle" — proved from the `n`-dimensional theorem `Fwd.determinate_iff` and the
equivalence `eq336_iff` (with `ψ₂ ≠ 0`). -/
theorem econ_determinate_iff [Nonempty Ω] {S : Sys36} (hψ2 : S.ψ2 ≠ 0) :
    EconDeterminate 𝔼 S ↔ EigenOut S.Ahat := by
  constructor
  · intro hD μ hμ
    by_contra hle
    push Not at hle
    obtain ⟨m, hm, hmb, hm0⟩ := exists_mode hle hμ
    obtain ⟨q, ⟨hXa, hJa, hPa, hXb, hJb, hPb, heq⟩, huniq⟩ :=
      hD 0 ⟨0, fun _ _ => by simp⟩ (fun t => by simp)
    have hx := (eq336_iff 𝔼 hψ2).mp heq
    obtain ⟨h1, h2, h3, h4⟩ := not_unique_of_mode 𝔼 hm hmb hm0 hx
      (zvec_adapted 𝔼 hXa hJa hPa) (zvec_bounded 𝔼 hXb hJb hPb)
    set x' := fun t i => zvec 𝔼 q.1 q.2.1 q.2.2 t i + fun _ => m t i with hx'
    have hz := zvec_of_sol 𝔼 h1
    have hsol : EconSol 𝔼 S 0 (fun t => x' t 0) (fun t => x' t 1) (fun t => x' t 3) := by
      obtain ⟨M, hM⟩ := h3
      refine ⟨fun t => h2 t 0, fun t => h2 t 1, fun t => h2 t 3, ⟨M, fun t ω => hM t 0 ω⟩,
        ⟨M, fun t ω => hM t 1 ω⟩, ⟨M, fun t ω => hM t 3 ω⟩, ?_⟩
      rw [eq336_iff 𝔼 hψ2, ← hz]
      exact h1
    have heq' := huniq (fun t => x' t 0, fun t => x' t 1, fun t => x' t 3) hsol
    apply h4
    rw [hz, ← heq']
  · intro hA f ⟨Mf, hf⟩ hfa
    obtain ⟨hwb, hwa⟩ := wvec_bounded_adapted 𝔼 (S := S) hf hfa
    obtain ⟨h1, h2, h3, h4⟩ := existsUnique_of_eigenOut 𝔼 hA hwb hwa
    set x := fwdVec 𝔼 S.Ahat⁻¹ (fun t => rvMul (-S.Ahat⁻¹) (wvec S f t)) with hxdef
    have hz := zvec_of_sol 𝔼 h1
    obtain ⟨M, hM⟩ := h3
    refine ⟨(fun t => x t 0, fun t => x t 1, fun t => x t 3),
      ⟨fun t => h2 t 0, fun t => h2 t 1, fun t => h2 t 3, ⟨M, fun t ω => hM t 0 ω⟩,
        ⟨M, fun t ω => hM t 1 ω⟩, ⟨M, fun t ω => hM t 3 ω⟩, ?_⟩, ?_⟩
    · rw [eq336_iff 𝔼 hψ2, ← hz]
      exact h1
    · rintro ⟨X', J', P'⟩ ⟨ha1, ha2, ha3, hb1, hb2, hb3, heq⟩
      have hzz := h4 _ ((eq336_iff 𝔼 hψ2).mp heq) (zvec_adapted 𝔼 ha1 ha2 ha3)
        (zvec_bounded 𝔼 hb1 hb2 hb3)
      have c0 : X' = fun t => x t 0 := funext fun t => congrFun (congrFun hzz t) 0
      have c1 : J' = fun t => x t 1 := funext fun t => congrFun (congrFun hzz t) 1
      have c3 : P' = fun t => x t 3 := funext fun t => congrFun (congrFun hzz t) 3
      rw [c0, c1, c3]

/-! ### The forward solutions (3.37)–(3.39) and the tracking claim of p. 378 -/

open scoped Matrix in
/-- Woodford (2003), eqs. (3.37)–(3.39), p. 376: the coefficients
`ψ_j = (Â⁻¹)ʲ(−Â⁻¹ â)`, component `i` (`i = 3`: inflation, `i = 0`: output gap). -/
noncomputable def psi (S : Sys36) (i : Fin 4) (k : ℕ) : ℝ :=
  ((S.Ahat⁻¹ ^ k) *ᵥ ((-S.Ahat⁻¹) *ᵥ S.ahat)) i

open scoped Matrix in
/-- Woodford (2003), (3.37): the `k`-th term of the forward series is `ψ_k E_t f_{t+k}`. -/
theorem fwd_term (S : Sys36) (f : ℕ → Ω → ℝ) (t k : ℕ) (i : Fin 4) (ω : Ω) :
    rvMul (S.Ahat⁻¹ ^ k) (fun j => 𝔼.E t (rvMul (-S.Ahat⁻¹) (wvec S f (t + k)) j)) i ω =
      psi S i k * 𝔼.E t (f (t + k)) ω := by
  simp only [psi, rvMul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [rvMul, wvec, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

open scoped Matrix in
/-- **Woodford (2003), eqs. (3.37)–(3.39), p. 376**: under determinacy (`Â` with all
eigenvalues outside the unit circle) the unique bounded equilibrium is the forward solution
`π_t − π̄ = ∑_j ψ^π_j E_t f_{t+j}`, `x_t − x̄ = ∑_j ψ^x_j E_t f_{t+j}` and
`ı̂_t − ī_t = φ_π(π_t − π̄) + φ_x(x_t − x̄)/4 = ∑_j ψ^i_j E_t f_{t+j}`, `ψ^i = φ_πψ^π + φ_xψ^x/4`,
the series converging absolutely (`f` is the forcing of (3.36)). -/
theorem eq337_339 {S : Sys36} (hψ2 : S.ψ2 ≠ 0) (hA : EigenOut S.Ahat)
    {f X J Pv : ℕ → Ω → ℝ} {Mf : ℝ} (hf : ∀ t ω, |f t ω| ≤ Mf) (hfa : 𝔼.Adapted f)
    (hsol : EconSol 𝔼 S f X J Pv) (t : ℕ) (ω : Ω) :
    HasSum (fun k => psi S 3 k * 𝔼.E t (f (t + k)) ω) (Pv t ω) ∧
      HasSum (fun k => psi S 0 k * 𝔼.E t (f (t + k)) ω) (X t ω) ∧
      HasSum (fun k => (S.φπ * psi S 3 k + S.φx / 4 * psi S 0 k) * 𝔼.E t (f (t + k)) ω)
        (S.φπ * Pv t ω + S.φx / 4 * X t ω) := by
  obtain ⟨hXa, hJa, hPa, hXb, hJb, hPb, heq⟩ := hsol
  obtain ⟨hwb, hwa⟩ := wvec_bounded_adapted 𝔼 (S := S) hf hfa
  obtain ⟨-, -, -, h4⟩ := existsUnique_of_eigenOut 𝔼 hA hwb hwa
  have hz := h4 _ ((eq336_iff 𝔼 hψ2).mp heq) (zvec_adapted 𝔼 hXa hJa hPa)
    (zvec_bounded 𝔼 hXb hJb hPb)
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hK⟩ := pow_entry_bound (S.Ahat⁻¹) (eigen_inv hA)
  set c := (-S.Ahat⁻¹) *ᵥ S.ahat with hc
  have hpsi : ∀ i k, |psi S i k| ≤ Cb * (∑ j, |c j|) * ρ ^ k := by
    intro i k
    simp only [psi, Matrix.mulVec, dotProduct]
    calc |∑ j, (S.Ahat⁻¹ ^ k) i j * c j| ≤ ∑ j, |(S.Ahat⁻¹ ^ k) i j * c j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, Cb * ρ ^ k * |c j| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hK k i j) (abs_nonneg _)
      _ = Cb * (∑ j, |c j|) * ρ ^ k := by rw [← Finset.mul_sum]; ring
  have hsum : ∀ i, Summable (fun k => psi S i k * 𝔼.E t (f (t + k)) ω) := fun i =>
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hρ0.le hρ1).mul_left (Cb * (∑ j, |c j|) * max Mf 0))
      (fun k => by
        rw [Real.norm_eq_abs, abs_mul]
        have e1 := hpsi i k
        have e2 := (𝔼.abs_E_le (fun ω => (hf (t + k) ω).trans (le_max_left Mf 0)) t ω)
        have e3 : 0 ≤ Cb * (∑ j, |c j|) := mul_nonneg hCb (Finset.sum_nonneg fun _ _ =>
          abs_nonneg _)
        calc |psi S i k| * |𝔼.E t (f (t + k)) ω| ≤ (Cb * (∑ j, |c j|) * ρ ^ k) * max Mf 0 :=
              mul_le_mul e1 e2 (abs_nonneg _) (mul_nonneg e3 (pow_nonneg hρ0.le _))
          _ = Cb * (∑ j, |c j|) * max Mf 0 * ρ ^ k := by ring)
  have hval : ∀ i, zvec 𝔼 X J Pv t i ω = ∑' k, psi S i k * 𝔼.E t (f (t + k)) ω := by
    intro i
    rw [hz]
    exact tsum_congr fun k => fwd_term 𝔼 S f t k i ω
  have hP : HasSum (fun k => psi S 3 k * 𝔼.E t (f (t + k)) ω) (Pv t ω) := by
    have := (hsum 3).hasSum
    rwa [← hval 3] at this
  have hX : HasSum (fun k => psi S 0 k * 𝔼.E t (f (t + k)) ω) (X t ω) := by
    have := (hsum 0).hasSum
    rwa [← hval 0] at this
  refine ⟨hP, hX, ?_⟩
  have := (hP.mul_left S.φπ).add (hX.mul_left (S.φx / 4))
  refine this.congr_fun fun k => ?_
  ring

/-- Woodford (2003), p. 378: with forcing identically zero — the intercept tracks
`ī_t = r̂ⁿ_t + π̄` (and the steady-state real-rate gap vanishes, see `steady_rate_gap`) —
the unique bounded equilibrium under a determinate rule has `π_t = π̄` and `x_t = x̄` at all
dates: inflation is completely stabilised with finite response coefficients. -/
theorem tracking_stabilises [Nonempty Ω] {S : Sys36} (hψ2 : S.ψ2 ≠ 0)
    (hA : EigenOut S.Ahat) {X J Pv : ℕ → Ω → ℝ} (hsol : EconSol 𝔼 S 0 X J Pv) :
    (∀ t, Pv t = 0) ∧ (∀ t, X t = 0) ∧ ∀ t, J t = 0 := by
  obtain ⟨q, -, huniq⟩ := (econ_determinate_iff 𝔼 hψ2).mpr hA 0 ⟨0, fun _ _ => by simp⟩
    (fun t => by simp)
  have h0 : EconSol 𝔼 S 0 0 0 0 := by
    refine ⟨fun t => by simp, fun t => by simp, fun t => by simp, ⟨0, fun _ _ => by simp⟩,
      ⟨0, fun _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩, fun t => ?_⟩
    simp [R36, S36]
  have e1 := huniq (X, J, Pv) hsol
  have e2 := huniq (0, 0, 0) h0
  have e : (X, J, Pv) = ((0 : ℕ → Ω → ℝ), (0 : ℕ → Ω → ℝ), (0 : ℕ → Ω → ℝ)) := e1.trans e2.symm
  simp only [Prod.mk.injEq] at e
  exact ⟨fun t => by rw [e.2.2]; rfl, fun t => by rw [e.1]; rfl, fun t => by rw [e.2.1]; rfl⟩

open scoped Matrix in
/-- Woodford (2003), p. 376: if every eigenvalue of `A` lies outside the unit circle, `1` is not
an eigenvalue, so `I − A` is invertible. -/
theorem det_one_sub_ne_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : EigenOut A) :
    (1 - A).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  have h := hA 1 ((eigen_iff _ 1).mpr ⟨fun i => (v i : ℂ), fun h => hv0 (funext fun i => by
    have := congrFun h i; simpa using this), by rw [ofReal_mulVec, ← hv]; funext i; simp⟩)
  rw [norm_one] at h
  exact lt_irrefl _ h

open scoped Matrix in
/-- Woodford (2003), p. 378 (complete stabilisation with a constant forcing): under a
determinate rule, a constant forcing `f ≡ c` — for instance the constant steady-state real-rate
gap that remains when `ī_t = r̂ⁿ_t + π̄` (`steady_rate_gap`) — gives an equilibrium that is
constant over time: `ẑ_t = (I − Â)⁻¹ â c`, so inflation is completely stabilised (at a constant
level). -/
theorem const_forcing [Nonempty Ω] {S : Sys36} (hψ2 : S.ψ2 ≠ 0) (hA : EigenOut S.Ahat)
    (c : ℝ) {X J Pv : ℕ → Ω → ℝ} (hsol : EconSol 𝔼 S (fun _ _ => c) X J Pv) :
    ∀ t, Pv t = (fun _ => ((1 - S.Ahat)⁻¹ *ᵥ (c • S.ahat)) 3) ∧
      X t = (fun _ => ((1 - S.Ahat)⁻¹ *ᵥ (c • S.ahat)) 0) ∧
      J t = (fun _ => ((1 - S.Ahat)⁻¹ *ᵥ (c • S.ahat)) 1) := by
  set zs := (1 - S.Ahat)⁻¹ *ᵥ (c • S.ahat) with hzs
  have hu : IsUnit (1 - S.Ahat).det := isUnit_iff_ne_zero.mpr (det_one_sub_ne_zero hA)
  have hfix : zs = S.Ahat *ᵥ zs + c • S.ahat := by
    have h1 : (1 - S.Ahat) *ᵥ zs = c • S.ahat := by
      rw [hzs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    rw [← h1]; abel
  have hf : ∀ t ω, |(fun _ _ => c : ℕ → Ω → ℝ) t ω| ≤ |c| := fun _ _ => le_rfl
  have hfa : 𝔼.Adapted (fun _ _ => c : ℕ → Ω → ℝ) := fun t => 𝔼.const t c
  obtain ⟨hwb, hwa⟩ := wvec_bounded_adapted 𝔼 (S := S) hf hfa
  obtain ⟨-, -, -, h4⟩ := existsUnique_of_eigenOut 𝔼 hA hwb hwa
  obtain ⟨hXa, hJa, hPa, hXb, hJb, hPb, heq⟩ := hsol
  have hz := h4 _ ((eq336_iff 𝔼 hψ2).mp heq) (zvec_adapted 𝔼 hXa hJa hPa)
    (zvec_bounded 𝔼 hXb hJb hPb)
  have hcs : ExpSys 𝔼 S.Ahat (wvec S (fun _ _ => c)) (fun _ i _ => zs i) := by
    intro t i
    rw [𝔼.const]
    funext ω
    have := congrFun hfix i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Pi.add_apply, rvMul_apply, wvec, Pi.smul_apply, smul_eq_mul]
    rw [this]
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hc := h4 _ hcs (fun t i => 𝔼.const t _) ⟨∑ i, |zs i|, fun t i ω =>
    Finset.single_le_sum (f := fun i => |zs i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)⟩
  intro t
  have e : zvec 𝔼 X J Pv = fun _ i _ => zs i := hz.trans hc.symm
  exact ⟨congrFun (congrFun e t) 3, congrFun (congrFun e t) 0, congrFun (congrFun e t) 1⟩

/-! ### Steady states, deviations and the forcing of (3.36) -/

omit 𝔼 in
/-- Woodford (2003), p. 376 (`x̄`, `Ī` "corresponding to steady inflation at the rate `π̄`"): in
a steady state of the gap equations — corrected (3.28), (3.29)–(3.31), (3.27) and (3.17), all
variables constant — the real-rate gap is `r̃̄ = −η_λ Ī/k`, and `Ī ≠ 0` whenever `π̄ ≠ 0`
(given `c' ≠ 0`, `k ≠ 0`, `ρ_y + σ⁻¹ ≠ 0`, `1 − ψ₁ + ψ₂ ≠ 0`). Hence the steady-state real-rate
gap is nonzero when `π̄ ≠ 0` and `η_λ ≠ 0`. -/
theorem steady_rate_gap (P : Par) (hcp : P.cp ≠ 0) (hk : P.k ≠ 0) (hρσ : P.ρy + P.σ⁻¹ ≠ 0)
    {ηl ηy ηk ω ξ0 ξ1 ψ1 ψ2 xbar Ibar Kbar lbar rbar sbar πbar : ℝ}
    (h29 : Ibar = P.k * Kbar) (h30 : lbar = -P.σ⁻¹ * (xbar - Ibar))
    (h31 : rbar = lbar - (lbar + ηl * Kbar))
    (h28 : lbar + P.eps * Kbar = P.β * (1 - P.δ) * (lbar + ηl * Kbar) +
      P.cp * (P.ρy * (xbar + ηy * Kbar) - P.ρk * Kbar) + P.β * P.eps * ((Kbar + ηk * Kbar) - Kbar))
    (h27 : sbar = (ω + P.σ⁻¹) * xbar - P.σ⁻¹ * Ibar)
    (h17 : πbar = ξ0 * sbar - ξ1 * sbar + ψ1 * πbar - ψ2 * πbar) (hden : 1 - ψ1 + ψ2 ≠ 0)
    (hπ : πbar ≠ 0) : rbar = -(ηl * Ibar / P.k) ∧ Ibar ≠ 0 := by
  have hK : Kbar = Ibar / P.k := by rw [h29]; field_simp
  refine ⟨by rw [h31, hK]; ring, fun hI => hπ ?_⟩
  have hK0 : Kbar = 0 := by rw [hK, hI, zero_div]
  rw [hK0] at h28
  have h1 : P.cp * (lbar - P.ρy * xbar) = 0 := by
    simp only [Par.cp] at h28 ⊢; linear_combination h28
  have h2 : lbar = P.ρy * xbar := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hcp
    · linarith
  have h3 : (P.ρy + P.σ⁻¹) * xbar = 0 := by rw [hI] at h30; linear_combination h2.symm.trans h30
  have hx : xbar = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hρσ
    · exact h
  have hs : sbar = 0 := by rw [h27, hx, hI]; ring
  rw [hs] at h17
  have : πbar * (1 - ψ1 + ψ2) = 0 := by linear_combination h17
  rcases mul_eq_zero.mp this with h | h
  · exact h
  · exact absurd h hden

/-- Woodford (2003), (3.34)–(3.36) and fn. 38: writing the rule in deviations from a steady
state with real-rate gap `r̃̄`, `r̃_t − r̃̄ = −(v_t + r̃̄) − E_t(π_{t+1} − π̄) + φ_π(π_t − π̄)
+ φ_x(x_t − x̄)/4` with `v_t = r̂ⁿ_t − ī_t + π̄` (`eq334`): the forcing of (3.36) is
`v_t + r̃̄`, which is the printed `r̂ⁿ_t − ī_t + π̄` only when `r̃̄ = 0` (cf. `steady_rate_gap`). -/
theorem deviation_forcing {πbar xbar φπ φx rbar : ℝ} {rt v π x : ℕ → Ω → ℝ}
    (h : ∀ t, rt t = -v t - 𝔼.E t (π (t + 1) - fun _ => πbar) + φπ • (π t - fun _ => πbar) +
      (φx / 4) • (x t - fun _ => xbar)) (t : ℕ) :
    rt t - (fun _ => rbar) = -(v t + fun _ => rbar) - 𝔼.E t (π (t + 1) - fun _ => πbar) +
      φπ • (π t - fun _ => πbar) + (φx / 4) • (x t - fun _ => xbar) := by
  rw [h t]; abel

/-- Woodford (2003), fn. 38, p. 376 ("all of these equations continue to be valid when we replace
variables by the difference of those variables from their steady-state values"), for (3.32):
if `(ȳ, ȷ̄, r̄)` is a steady state, the deviations satisfy (3.32) with the same `A`, `a`. -/
theorem deviation_332 {A00 A01 A10 A11 a0 a1 yb jb rb : ℝ} {y j r : ℕ → Ω → ℝ}
    (h : ∀ t, 𝔼.E t (y (t + 1)) = A00 • y t + A01 • j t + a0 • r t ∧
      𝔼.E t (j (t + 1)) = A10 • y t + A11 • j t + a1 • r t)
    (hs1 : yb = A00 * yb + A01 * jb + a0 * rb) (hs2 : jb = A10 * yb + A11 * jb + a1 * rb)
    (t : ℕ) :
    𝔼.E t (y (t + 1) - fun _ => yb) = A00 • (y t - fun _ => yb) + A01 • (j t - fun _ => jb) +
        a0 • (r t - fun _ => rb) ∧
      𝔼.E t (j (t + 1) - fun _ => jb) = A10 • (y t - fun _ => yb) +
        A11 • (j t - fun _ => jb) + a1 • (r t - fun _ => rb) := by
  constructor
  · rw [map_sub, 𝔼.const, (h t).1]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -hs1
  · rw [map_sub, 𝔼.const, (h t).2]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -hs2

/-- Woodford (2003), fn. 38, p. 376, for (3.17): if `(π̄, s̄)` is a steady state
(`π̄ = ξ₀s̄ − ξ₁s̄ + ψ₁π̄ − ψ₂π̄`), the deviations satisfy (3.17) with the same coefficients. -/
theorem deviation_317 {ξ0 ξ1 ψ1 ψ2 πb sb : ℝ} {π sc : ℕ → Ω → ℝ}
    (h : ∀ t, π t = ξ0 • sc t - ξ1 • 𝔼.E t (sc (t + 1)) + ψ1 • 𝔼.E t (π (t + 1)) -
      ψ2 • 𝔼.E t (π (t + 2)))
    (hs : πb = ξ0 * sb - ξ1 * sb + ψ1 * πb - ψ2 * πb) (t : ℕ) :
    π t - (fun _ => πb) = ξ0 • (sc t - fun _ => sb) - ξ1 • 𝔼.E t (sc (t + 1) - fun _ => sb) +
      ψ1 • 𝔼.E t (π (t + 1) - fun _ => πb) - ψ2 • 𝔼.E t (π (t + 2) - fun _ => πb) := by
  simp only [map_sub, 𝔼.const]
  rw [h t]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination -hs

/-! ### The model's system (3.36) -/

/-- Woodford (2003), p. 375: the system (3.36) of the investment model — (3.32)'s `A = Amat`,
`a = avec`, (3.27)'s `m_Y = ω + σ⁻¹`, `m_I = σ⁻¹`, and the coefficients of (3.17) and (3.33). -/
noncomputable def modelSys (P : Par) (ηl ηy ηk ω ξ0 ξ1 ψ1 ψ2 φπ φx : ℝ) : Sys36 :=
  ⟨Amat P ηl ηy ηk 0 0, Amat P ηl ηy ηk 0 1, Amat P ηl ηy ηk 1 0, Amat P ηl ηy ηk 1 1,
    avec P 0, avec P 1, ω + P.σ⁻¹, P.σ⁻¹, ξ0, ξ1, ψ1, ψ2, φπ, φx⟩

/-- **Woodford (2003), (3.36), p. 376**, for the investment model: with `ψ₂ ≠ 0`, the policy rule
(3.33)/(3.35) yields determinate equilibrium dynamics if and only if all four eigenvalues of `Â`
lie outside the unit circle. (`ψ₂ = βμ₂⁻¹ > 0` in Proposition 5.1.) -/
theorem determinacy_336 [Nonempty Ω] (P : Par) {ηl ηy ηk ω ξ0 ξ1 ψ1 ψ2 φπ φx : ℝ}
    (hψ2 : ψ2 ≠ 0) :
    EconDeterminate 𝔼 (modelSys P ηl ηy ηk ω ξ0 ξ1 ψ1 ψ2 φπ φx) ↔
      EigenOut (modelSys P ηl ηy ηk ω ξ0 ξ1 ψ1 ψ2 φπ φx).Ahat :=
  econ_determinate_iff 𝔼 hψ2

end Woodford.PolicyResponseDynamics.InvestmentNaturalRate
