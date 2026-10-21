/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.SurplusProcess

/-!
# Alternative surplus processes: backed and unbacked components

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.6, eqs. (5.82)–(5.84),
pp. 160–162.

The surplus is split into a backed component `s*` (the latent-variable process of §5.4 with
`β_s = 0`, debt `v*` repaid in full) and an unbacked AR(1) component `ŝ`:
`s̃ = s* + ŝ`, `s*_{t+1} = α v*_t + u*_{t+1}`, `ρ v*_{t+1} = v*_t − s*_{t+1}`, `ŝ_{t+1} = û_{t+1}`,
with AR(1) disturbances `u*`, `û`, in the frictionless model with one-period debt.

## Main results

* `AltModel`, `backed_surplusProc`, `alt_frictionless`.
* `alt_ma`: the moving-average representation (p. 161 display) with `vCoef_backed`.
* `backed_aRho` (`a(ρ) = 0`), `unbacked_aRho` (`a(ρ) = 1/(1 − ρη̂)`).
* `alt_E_s`, `alt_summable`: forecasts and the (absolutely convergent) present value of `s̃`.
* `alt_unexpected_inflation`: `ΔE_{t+1} π_{t+1} = −ε̂_{t+1}/(1 − ρη̂)`.
* `alt_vstar_pv`: `v*_t = E_t ∑_j ρʲ s*_{t+1+j}`, i.e. `v*_{t+1} = E_{t+1} ∑ ρʲ s*_{t+2+j}`;
  survey E44: `printed_e44_vstar` (with the printed sum starting at `s*_{t+1}` the identity
  forces `ε*_{t+1} = 0`), `printed_e44_v`.
* `alt_v_closed_form`: `v_t = η̂ û_t/(1 − ρη̂) + v*_t`, the present value of all surpluses; so
  `v ≠ v*` whenever `η̂ û_t ≠ 0` (`alt_v_ne_vstar`).
-/

namespace Cochrane.StickyPriceFiscal.AltSurplus

open Filter Topology SurplusProcess
open SharedTools (TVC)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §5.6, eqs. (5.82)–(5.84), p. 160: `i_t = E_t π_{t+1}`,
`ρ v_{t+1} = v_t − ΔE_{t+1} π_{t+1} − s̃_{t+1}`, `s̃ = s* + ŝ`, `s*_{t+1} = α v*_t + u*_{t+1}`,
`ρ v*_{t+1} = v*_t − s*_{t+1}`, `ŝ_{t+1} = û_{t+1}`, `u*_{t+1} = η* u*_t + ε*_{t+1}`,
`û_{t+1} = η̂ û_t + ε̂_{t+1}`. -/
def AltModel (ρ α ηs ηh : ℝ) (εs εh i π s v ss sh vs us uh : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1) ∧
    s (t + 1) = ss (t + 1) + sh (t + 1) ∧ ss (t + 1) = α • vs t + us (t + 1) ∧
    ρ • vs (t + 1) = vs t - ss (t + 1) ∧ sh (t + 1) = uh (t + 1) ∧
    us (t + 1) = ηs • us t + εs (t + 1) ∧ uh (t + 1) = ηh • uh t + εh (t + 1)

variable {ρ α ηs ηh : ℝ} {εs εh i π s v ss sh vs us uh : ℕ → Ω → ℝ}

/-- Cochrane (2023), (5.83)–(5.84), p. 160: the backed component is the surplus process
(5.22)–(5.24) with `β_s = 0`. -/
theorem backed_surplusProc (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh) :
    IsSurplusProc ρ α 0 ηs εs ss vs us := fun t => by
  obtain ⟨-, -, -, h4, h5, -, h7, -⟩ := h t
  exact ⟨h4, by rw [h5, zero_smul, add_zero], h7⟩

/-- Cochrane (2023), §5.6, p. 160: the inflation and debt equations are the frictionless model
of (5.27). -/
theorem alt_frictionless (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh) :
    Frictionless 𝔼 ρ i π s v := fun t => by
  obtain ⟨h1, h2, -⟩ := h t
  refine ⟨h1, ?_⟩
  rw [h2, surprise, ← h1]
  abel

/-- Cochrane (2023), §5.6, p. 161: with `û_0 = 0`, `û_t = ∑_{k<t} η̂ᵏ ε̂_{t−k}`. -/
theorem ar1_ma {η : ℝ} {u ε : ℕ → Ω → ℝ} (hu0 : u 0 = 0)
    (hur : ∀ t, u (t + 1) = η • u t + ε (t + 1)) (t : ℕ) : u t = ma (fun k => η ^ k) ε t := by
  induction t with
  | zero => rw [hu0, ma_zero]
  | succ t ih =>
    funext ω
    have h3 := congrFun (hur t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3
    rw [h3, ma_succ, ih,
      show (fun k => η ^ (k + 1)) = fun k => η * η ^ k + 0 * (0 : ℝ) from
        funext fun k => by ring, ma_add_mul]
    ring

/-- Cochrane (2023), §5.6, p. 161: the backed latent debt has moving-average coefficients
`vCoef = −ρ⁻¹ ∑_{i ≤ k} gⁱ η*^{k−i}`, i.e. `v*_{t+1} = −ρ⁻¹ ε*_{t+1}/((1 − gL)(1 − η* L))`. -/
theorem vCoef_backed (k : ℕ) :
    vCoef ρ α 0 ηs k = -ρ⁻¹ * geomConv (gRoot ρ α) ηs k := by
  simp only [vCoef]
  ring

/-- Cochrane (2023), §5.6, p. 161 (moving-average display): with zero pre-sample states,
`s̃_{t+1} = [(1 − ρ⁻¹L)/(1 − gL)] ε*_{t+1}/(1 − η* L) + ε̂_{t+1}/(1 − η̂ L)`; the backed
coefficients are `aCoef ρ α 0 η*` (by `aCoef_526` with `β_s = 0`). -/
theorem alt_ma (hρ : ρ ≠ 0) (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh)
    (hv0 : vs 0 = 0) (hus0 : us 0 = 0) (huh0 : uh 0 = 0) (t : ℕ) :
    s (t + 1) = ma (aCoef ρ α 0 ηs) εs (t + 1) + ma (fun k => ηh ^ k) εh (t + 1) ∧
      vs t = ma (vCoef ρ α 0 ηs) εs t := by
  have hP := ma_representation hρ (backed_surplusProc 𝔼 h) hv0 hus0 t
  obtain ⟨-, -, h3, -, -, h6, -, -⟩ := h t
  refine ⟨?_, hP.2.1⟩
  rw [h3, hP.2.2, h6, ar1_ma huh0 (fun t => (h t).2.2.2.2.2.2.2) (t + 1)]

/-- Cochrane (2023), §5.6, p. 161: "a(ρ) = 0 for the first term" — the backed component is
fully repaid. -/
theorem backed_aRho (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * ηs| < 1) :
    HasSum (fun k => ρ ^ k * aCoef ρ α 0 ηs k) 0 :=
  hasSum_aCoef hρ hα hη

/-- Cochrane (2023), §5.6, p. 161: "a(ρ) = 1/(1 − ρη̂) for the second term" (the book's
`1/(1 − ρ_s η̂)` is a typo, survey E44). -/
theorem unbacked_aRho (hη : |ρ * ηh| < 1) :
    HasSum (fun k : ℕ => ρ ^ k * ηh ^ k) (1 - ρ * ηh)⁻¹ := by
  simpa [mul_pow] using hasSum_geometric_of_abs_lt_one hη

/-- Cochrane (2023), §5.6, p. 161: the backed latent debt is the present value of backed
surpluses, `v*_t = ∑_j ρʲ E_t s*_{t+1+j}`; dated `t + 1` this is
`v*_{t+1} = E_{t+1} ∑_j ρʲ s*_{t+2+j}` (survey E44: the sum starts at `s*_{t+2}`). -/
theorem alt_vstar_pv (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * ηs| < 1)
    (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh) (hεa : 𝔼.Adapted εs)
    (hε : MeanZero 𝔼 εs) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (us 0) = us 0) (t : ℕ)
    (ω : Ω) : HasSum (fun j => ρ ^ j * 𝔼.E t (ss (t + 1 + j)) ω) (vs t ω) :=
  vstar_eq_pv 𝔼 hρ hα hη (backed_surplusProc 𝔼 h) hεa hε hv0 hu0 t ω

/-- Cochrane (2023), §5.6, p. 161, survey E44: the printed `v*_{t+1} = E_{t+1} ∑_j ρʲ s*_{t+1+j}`
is false. The printed sum equals `v*_t`, so the identity would force `v*_{t+1} = v*_t`, whose
innovation `−ρ⁻¹ ε*_{t+1}` must then vanish: the identity holds only if `ε*_{t+1} = 0`. -/
theorem printed_e44_vstar (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hη : |ρ * ηs| < 1)
    (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh) (hεa : 𝔼.Adapted εs)
    (hε : MeanZero 𝔼 εs) (hv0 : 𝔼.E 0 (vs 0) = vs 0) (hu0 : 𝔼.E 0 (us 0) = us 0) (t : ℕ)
    (hpr : ∀ ω, vs (t + 1) ω = ∑' j, ρ ^ j * 𝔼.E (t + 1) (ss (t + 1 + j)) ω) :
    εs (t + 1) = 0 := by
  have hP := backed_surplusProc 𝔼 h
  have had := proc_adapted 𝔼 hρ hP hεa hv0 hu0
  -- the printed sum is `s*_{t+1} + ρ v*_{t+1} = v*_t`
  have hsum : ∀ ω, HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (ss (t + 1 + j)) ω) (vs t ω) := by
    intro ω
    have H1 := vstar_eq_pv 𝔼 hρ hα hη hP hεa hε hv0 hu0 (t + 1) ω
    rw [← hasSum_nat_add_iff' 1]
    have hr := congrFun (hP t).2.1 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
    convert H1.mul_left ρ using 1
    · funext n
      rw [show t + 1 + (n + 1) = t + 1 + 1 + n by omega, pow_succ]
      ring
    · simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero,
        had.2.2 t]
      linarith
  have hvv : vs (t + 1) = vs t := funext fun ω => by rw [hpr ω, (hsum ω).tsum_eq]
  have hE := congrArg (fun x => x - 𝔼.E t x) (vstar_rec hP t)
  simp only [map_sub, map_add, map_smul, hvv, had.2.1 t, sub_self, hε t,
    smul_zero, add_zero, (hP t).2.2, had.1 t] at hE
  have e : (1 - α) • vs t + (0 : ℝ) • εs (t + 1) - (ηs • us t + εs (t + 1)) -
      ((1 - α) • vs t - ηs • us t) = -εs (t + 1) := by
    rw [zero_smul, add_zero]
    abel
  rw [e] at hE
  exact neg_eq_zero.mp hE.symm

/-- Cochrane (2023), §5.6, p. 161, survey E44: the printed sum for the value of debt starting
at `s̃_{t+1}` equals `s̃_{t+1} + ρ v_{t+1}`, not `v_{t+1}`. -/
theorem printed_e44_v (t : ℕ) (ω : Ω)
    (hs1 : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1))
    (H1 : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (s (t + 1 + 1 + j)) ω) (v (t + 1) ω)) :
    HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) ω) (s (t + 1) ω + ρ * v (t + 1) ω) := by
  rw [← hasSum_nat_add_iff' 1]
  convert H1.mul_left ρ using 1
  · funext n
    rw [show t + 1 + (n + 1) = t + 1 + 1 + n by omega, pow_succ]
    ring
  · simp [hs1]

/-- Cochrane (2023), §5.6, p. 161: forecasts of the total surplus,
`E_r s̃_{r+1+j} = E_r s*_{r+1+j} + η̂^{1+j} û_r`. -/
theorem alt_E_s (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh)
    (hεh : MeanZero 𝔼 εh) (huh : 𝔼.Adapted uh) (r j : ℕ) :
    𝔼.E r (s (r + 1 + j)) = 𝔼.E r (ss (r + 1 + j)) + ηh ^ (1 + j) • uh r := by
  have hAR : 𝔼.IsAR1 ηh uh :=
    ⟨huh, fun t => by rw [(h t).2.2.2.2.2.2.2, map_add, map_smul, huh t, hεh t, add_zero]⟩
  obtain ⟨-, -, h3, -, -, h6, -, -⟩ := h (r + j)
  rw [show r + 1 + j = r + j + 1 by omega, h3, h6, map_add,
    show r + j + 1 = r + (1 + j) by omega, 𝔼.ar1_iterate hAR r (1 + j)]

/-- Cochrane (2023), §5.6, p. 161: the discounted total-surplus forecasts are absolutely
summable. -/
theorem alt_summable (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hηs : |ρ * ηs| < 1)
    (hηh : |ρ * ηh| < 1) (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh)
    (hεa : 𝔼.Adapted εs) (hε : MeanZero 𝔼 εs) (hv0 : 𝔼.E 0 (vs 0) = vs 0)
    (hu0 : 𝔼.E 0 (us 0) = us 0) (hεh : MeanZero 𝔼 εh) (huh : 𝔼.Adapted uh) (r : ℕ)
    (ω : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E r (s (r + 1 + j)) ω)
      (vs r ω + ηh * (1 - ρ * ηh)⁻¹ * uh r ω) := by
  have H := (alt_vstar_pv 𝔼 hρ hα hηs h hεa hε hv0 hu0 r ω).add
    ((hasSum_geometric_of_abs_lt_one hηh).mul_left (ηh * uh r ω))
  convert H using 1
  · funext j
    rw [alt_E_s 𝔼 h hεh huh r j, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_pow, pow_add]
    ring
  · ring

/-- Cochrane (2023), §5.6, p. 161: unexpected inflation comes only from the unbacked component,
`ΔE_{t+1} π_{t+1} = −ε̂_{t+1}/(1 − ρη̂)`, for any debt path satisfying the transversality
condition. -/
theorem alt_unexpected_inflation (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hηs : |ρ * ηs| < 1)
    (hηh : |ρ * ηh| < 1) (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh)
    (hεa : 𝔼.Adapted εs) (hε : MeanZero 𝔼 εs) (hv0 : 𝔼.E 0 (vs 0) = vs 0)
    (hu0 : 𝔼.E 0 (us 0) = us 0) (hεh : MeanZero 𝔼 εh) (huh : 𝔼.Adapted uh)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) :
    surprise 𝔼 π t = -((1 - ρ * ηh)⁻¹ • εh (t + 1)) := by
  have hP := backed_surplusProc 𝔼 h
  have had := proc_adapted 𝔼 hρ hP hεa hv0 hu0
  have hAR : 𝔼.IsAR1 ηh uh :=
    ⟨huh, fun t => by rw [(h t).2.2.2.2.2.2.2, map_add, map_smul, huh t, hεh t, add_zero]⟩
  have hs1 : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
    rw [(h t).2.2.1, map_add, had.2.2 t, (h t).2.2.2.2.2.1, huh (t + 1)]
  funext ω
  have H := unexpected_inflation_527 𝔼 (alt_frictionless 𝔼 h) hv htvc t hs1 ω
    (alt_summable 𝔼 hρ hα hηs hηh h hεa hε hv0 hu0 hεh huh t ω).summable
    (by simpa [add_assoc] using
      (alt_summable 𝔼 hρ hα hηs hηh h hεa hε hv0 hu0 hεh huh (t + 1) ω).summable)
  have H2 := (innov_pv 𝔼 hρ hα hηs hP hεa hε hv0 hu0 t ω).add
    ((hasSum_geometric_of_abs_lt_one hηh).mul_right (εh (t + 1) ω))
  have H3 : HasSum
      (fun j => ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω))
      (0 * εs (t + 1) ω + (1 - ρ * ηh)⁻¹ * εh (t + 1) ω) := by
    convert H2 using 1
    funext j
    have e1 : 𝔼.E (t + 1) (s (t + 1 + j)) = 𝔼.E (t + 1) (ss (t + 1 + j)) + ηh ^ j • uh (t + 1) := by
      obtain ⟨-, -, h3, -, -, h6, -, -⟩ := h (t + j)
      rw [show t + 1 + j = t + j + 1 by omega, h3, h6, map_add,
        show t + j + 1 = t + 1 + j by omega, 𝔼.ar1_iterate hAR (t + 1) j]
    have hr := congrFun (h t).2.2.2.2.2.2.2 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hr
    rw [e1, alt_E_s 𝔼 h hεh huh t j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hr, mul_pow, pow_add]
    ring
  have := H.unique H3
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Cochrane (2023), §5.6, p. 161: in equilibrium (debt satisfying the transversality
condition) the value of debt is the present value of all surpluses and equals
`v_t = η̂ û_t/(1 − ρη̂) + v*_t` ("each value of debt cumulates its own surplus"). -/
theorem alt_v_closed_form (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hηs : |ρ * ηs| < 1)
    (hηh : |ρ * ηh| < 1) (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh)
    (hεa : 𝔼.Adapted εs) (hε : MeanZero 𝔼 εs) (hv0 : 𝔼.E 0 (vs 0) = vs 0)
    (hu0 : 𝔼.E 0 (us 0) = us 0) (hεh : MeanZero 𝔼 εh) (huh : 𝔼.Adapted uh)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) (v t ω) ∧
      v t ω = ηh * (1 - ρ * ηh)⁻¹ * uh t ω + vs t ω := by
  have HS := alt_summable 𝔼 hρ hα hηs hηh h hεa hε hv0 hu0 hεh huh t ω
  have Hv := hasSum_pv 𝔼 hv (frictionless_debt 𝔼 (alt_frictionless 𝔼 h)) (E_surprise 𝔼 π) t ω
    HS.summable (htvc t ω)
  refine ⟨Hv, ?_⟩
  rw [Hv.unique HS]
  ring

/-- Cochrane (2023), §5.6, p. 161 ("The state variable is not equal to the value of debt"):
whenever `η̂ û_t ≠ 0`, `v_t ≠ v*_t`. -/
theorem alt_v_ne_vstar (hρ : ρ ≠ 0) (hα : |1 - α| < 1) (hηs : |ρ * ηs| < 1)
    (hηh : |ρ * ηh| < 1) (h : AltModel 𝔼 ρ α ηs ηh εs εh i π s v ss sh vs us uh)
    (hεa : 𝔼.Adapted εs) (hε : MeanZero 𝔼 εs) (hv0 : 𝔼.E 0 (vs 0) = vs 0)
    (hu0 : 𝔼.E 0 (us 0) = us 0) (hεh : MeanZero 𝔼 εh) (huh : 𝔼.Adapted uh)
    (hv : 𝔼.Adapted v) (htvc : TVC 𝔼 ρ v) (t : ℕ) (ω : Ω) (hne : ηh * uh t ω ≠ 0) :
    v t ω ≠ vs t ω := by
  rw [(alt_v_closed_form 𝔼 hρ hα hηs hηh h hεa hε hv0 hu0 hεh huh hv htvc t ω).2]
  intro heq
  have hpos : 0 < 1 - ρ * ηh := by linarith [(abs_lt.mp hηh).2]
  have : ηh * (1 - ρ * ηh)⁻¹ * uh t ω = 0 := by linarith
  rw [mul_right_comm] at this
  exact (mul_ne_zero hne (inv_ne_zero hpos.ne')) this

end Cochrane.StickyPriceFiscal.AltSurplus
