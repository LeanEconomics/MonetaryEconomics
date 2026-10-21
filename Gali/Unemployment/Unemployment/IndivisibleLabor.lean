/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Indivisible labour and the participation decision

Galí (2015), Chapter 7, §7.1.1, pp. 201–204, and the participation condition of §7.1.2,
p. 204. Each household has members `(j, s) ∈ [0, 1] × [0, 1]`; member `(j, s)` suffers the
disutility `χ s^φ` if employed (`χ > 0`, `φ > 0`). With full risk sharing the household's
period utility is the integral of its members' utilities, and with the employed members of
type `j` being `s ∈ [0, N(j)]`,

  `∫₀^{N(j)} χ s^φ ds = χ N(j)^{1+φ}/(1 + φ)`,

so the household's utility is exactly the Chapter 6 utility (p. 202). Member `(j, s)` is
willing to work iff `W(j)/P ≥ χ C^σ s^φ` (p. 204); the set of willing members is exactly the
interval `[0, L(j)]`, with `L(j)` the marginal participant defined by (5),
`W(j)/P = χ C^σ L(j)^φ`.

## Main results

* `integral_disutility`: `∫₀^N χ s^φ ds = χ N^{1+φ}/(1 + φ)` (a genuine interval integral,
  any real `N`, `φ > −1`).
* `householdUtility_eq_ch6`: the indivisible-labour household utility equals the Chapter 6
  utility `U(C, {N(j)}; Z) = (u(C) − χ ∫₀¹ N(j)^{1+φ}/(1+φ) dj) Z`.
* `hasDerivAt_disutility`: the marginal disutility of employing one more member is `χ N^φ`.
* `hasDerivAt_crra`, `marginal_value`: the marginal value to the household of member `s`
  working at real wage `ω` is `C^{−σ} ω − χ s^φ` (utility units), so
  `participates_iff`: member `s` participates iff `ω ≥ χ C^σ s^φ` (p. 204).
* `eq5_iff`: (5) has the unique nonnegative solution `L = (ω/(χ C^σ))^{1/φ}`.
* `participation_set_eq`: `{s ≥ 0 | χ C^σ s^φ ≤ ω} = [0, L]`, and
  `participation_set_unit`: within the unit interval of members it is `[0, min L 1]`.
* `marginal_indifferent`, `inframarginal_strict`, `supramarginal_refuses`: the marginal
  participant is indifferent; members below strictly gain, members above strictly lose.
* `laborForce_le_one_iff`: `L ≤ 1` iff `ω ≤ χ C^σ`.
-/

namespace Gali.Unemployment.IndivisibleLabor

/-! ### The disutility integral (p. 202) -/

/-- Galí (2015), p. 202: the total disutility of the employed members `s ∈ [0, N]` of a
labour type, `∫₀^N χ s^φ ds = χ N^{1+φ}/(1 + φ)`, for every real `N` and `φ > −1`
(in the model `φ > 0`, `N ∈ [0, 1]`). -/
theorem integral_disutility {χ φ : ℝ} (hφ : -1 < φ) (N : ℝ) :
    ∫ s in (0 : ℝ)..N, χ * s ^ φ = χ * N ^ (1 + φ) / (1 + φ) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hφ)]
  have h0 : (0 : ℝ) ^ (φ + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, sub_zero, add_comm φ 1]
  ring

/-- Galí (2015), p. 202: the period utility of consumption, `(C^{1−σ} − 1)/(1 − σ)`, with its
limit `log C` at `σ = 1`. -/
noncomputable def crra (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 202, first line: the indivisible-labour household's period utility, the
integral of its members' utilities, `(u(C) − χ ∫₀¹ ∫₀^{N(j)} s^φ ds dj) Z`. -/
noncomputable def householdUtility (σ χ φ C Z : ℝ) (N : ℝ → ℝ) : ℝ :=
  (crra σ C - χ * ∫ j in (0 : ℝ)..1, ∫ s in (0 : ℝ)..N j, s ^ φ) * Z

/-- Galí (2015), p. 202, second line (the Chapter 6 period utility):
`(u(C) − χ ∫₀¹ N(j)^{1+φ}/(1 + φ) dj) Z`. -/
noncomputable def ch6Utility (σ χ φ C Z : ℝ) (N : ℝ → ℝ) : ℝ :=
  (crra σ C - χ * ∫ j in (0 : ℝ)..1, N j ^ (1 + φ) / (1 + φ)) * Z

/-- Galí (2015), p. 202: with indivisible labour and full risk sharing, the household's
utility equals the Chapter 6 utility, for every employment profile `N(·)` (no integrability
hypothesis is needed: the inner integrals agree pointwise). -/
theorem householdUtility_eq_ch6 {σ χ φ : ℝ} (hφ : -1 < φ) (C Z : ℝ) (N : ℝ → ℝ) :
    householdUtility σ χ φ C Z N = ch6Utility σ χ φ C Z N := by
  unfold householdUtility ch6Utility
  have h : ∀ j, ∫ s in (0 : ℝ)..N j, s ^ φ = N j ^ (1 + φ) / (1 + φ) := fun j => by
    have := integral_disutility (χ := 1) hφ (N j)
    simpa using this
  simp_rw [h]

/-- Galí (2015), p. 204: the marginal disutility of employing one more member of a type with
`N` members employed is `χ N^φ` (the disutility of the marginal member), for `φ > 0`. -/
theorem hasDerivAt_disutility {χ φ : ℝ} (hφ : 0 < φ) (N : ℝ) :
    HasDerivAt (fun M => ∫ s in (0 : ℝ)..M, χ * s ^ φ) (χ * N ^ φ) N := by
  have hfun : (fun M => ∫ s in (0 : ℝ)..M, χ * s ^ φ) = fun M => χ * M ^ (1 + φ) / (1 + φ) :=
    funext fun M => integral_disutility (by linarith) M
  rw [hfun]
  have h1 : HasDerivAt (fun M : ℝ => M ^ (1 + φ)) ((1 + φ) * N ^ (1 + φ - 1)) N :=
    Real.hasDerivAt_rpow_const (Or.inr (by linarith))
  have h2 := (h1.const_mul χ).div_const (1 + φ)
  refine h2.congr_deriv ?_
  have : (1 : ℝ) + φ ≠ 0 := by linarith
  rw [show 1 + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 204: the marginal utility of consumption is `C^{−σ}`, for `C > 0` and
every `σ` (including the logarithmic case `σ = 1`). -/
theorem hasDerivAt_crra (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (crra σ) (C ^ (-σ)) C := by
  by_cases hσ : σ = 1
  · have hfun : crra σ = Real.log := funext fun x => by simp [crra, hσ]
    rw [hfun, hσ, Real.rpow_neg hC.le, Real.rpow_one]
    exact Real.hasDerivAt_log hC.ne'
  · have hfun : crra σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [crra, hσ]
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - σ)) ((1 - σ) * C ^ (1 - σ - 1)) C :=
      Real.hasDerivAt_rpow_const (Or.inl hC.ne')
    have h2 := (h1.sub_const 1).div_const (1 - σ)
    refine h2.congr_deriv ?_
    have : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.mpr (Ne.symm hσ)
    rw [show 1 - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), p. 204 (using the household's welfare as the criterion): if the household's
consumption is `C₀ + ω M` when its members `s ∈ [0, M]` work at the real wage `ω`, the marginal
value of the member `s = M` working is `C^{−σ} ω − χ M^φ`, `C = C₀ + ω M > 0`. -/
theorem marginal_value {σ χ φ C₀ ω : ℝ} (hφ : 0 < φ) {M : ℝ} (hC : 0 < C₀ + ω * M) :
    HasDerivAt (fun K => crra σ (C₀ + ω * K) - ∫ s in (0 : ℝ)..K, χ * s ^ φ)
      ((C₀ + ω * M) ^ (-σ) * ω - χ * M ^ φ) M := by
  have hlin : HasDerivAt (fun K : ℝ => C₀ + ω * K) ω M := by
    simpa using ((hasDerivAt_id M).const_mul ω).const_add C₀
  have hc := (hasDerivAt_crra σ hC).comp M hlin
  exact HasDerivAt.sub hc (hasDerivAt_disutility hφ M)

/-- Galí (2015), p. 204: member `s` (disutility `χ s^φ`) gains weakly from working iff the
real wage exceeds the disutility expressed in consumption units:
`C^{−σ} ω − χ s^φ ≥ 0 ⟺ ω ≥ χ C^σ s^φ`, for `C > 0`. -/
theorem participates_iff {σ χ φ C ω s : ℝ} (hC : 0 < C) :
    0 ≤ C ^ (-σ) * ω - χ * s ^ φ ↔ χ * C ^ σ * s ^ φ ≤ ω := by
  have hpos : 0 < C ^ σ := Real.rpow_pos_of_pos hC σ
  have hinv : C ^ (-σ) = (C ^ σ)⁻¹ := Real.rpow_neg hC.le σ
  rw [hinv, sub_nonneg]
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_left h hpos.le
    rw [← mul_assoc (C ^ σ) (C ^ σ)⁻¹, mul_inv_cancel₀ hpos.ne', one_mul] at this
    linarith [show χ * C ^ σ * s ^ φ = C ^ σ * (χ * s ^ φ) by ring]
  · intro h
    have h' : χ * s ^ φ * C ^ σ ≤ ω := by linarith
    rw [← le_div_iff₀ hpos] at h'
    rwa [inv_mul_eq_div]

/-! ### The marginal participant (5) -/

/-- Galí (2015), eq. (5), p. 204: the marginal supplier of type-`j` labour,
`L = (ω/(χ C^σ))^{1/φ}`, where `ω = W(j)/P`. -/
noncomputable def laborForce (σ χ φ C ω : ℝ) : ℝ := (ω / (χ * C ^ σ)) ^ φ⁻¹

/-- Galí (2015), eq. (5), p. 204: the marginal participant is nonnegative. -/
theorem laborForce_nonneg {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω) :
    0 ≤ laborForce σ χ φ C ω :=
  Real.rpow_nonneg (div_nonneg hω (mul_pos hχ (Real.rpow_pos_of_pos hC σ)).le) _

/-- Galí (2015), eq. (5), p. 204: `L^φ = ω/(χ C^σ)`. -/
theorem laborForce_rpow {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω) (hφ : 0 < φ) :
    laborForce σ χ φ C ω ^ φ = ω / (χ * C ^ σ) :=
  Real.rpow_inv_rpow (div_nonneg hω (mul_pos hχ (Real.rpow_pos_of_pos hC σ)).le) hφ.ne'

/-- Galí (2015), eq. (5), p. 204: for `L ≥ 0`, `ω = χ C^σ L^φ` holds iff `L` is the marginal
participant `(ω/(χ C^σ))^{1/φ}`; so (5) determines `L(j)` uniquely. -/
theorem eq5_iff {σ χ φ C ω L : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω) (hφ : 0 < φ)
    (hL : 0 ≤ L) : ω = χ * C ^ σ * L ^ φ ↔ L = laborForce σ χ φ C ω := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  constructor
  · intro h
    have hq : ω / (χ * C ^ σ) = L ^ φ := by
      rw [h]
      field_simp
    unfold laborForce
    rw [hq, Real.rpow_rpow_inv hL hφ.ne']
  · intro h
    rw [h, laborForce_rpow hχ hC hω hφ]
    field_simp

/-- Galí (2015), p. 204: the set of members `s ≥ 0` willing to work at real wage `ω > 0`,
`{s ≥ 0 | χ C^σ s^φ ≤ ω}`, is exactly the interval `[0, L]`, `L` given by (5). -/
theorem participation_set_eq {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) :
    {s : ℝ | 0 ≤ s ∧ χ * C ^ σ * s ^ φ ≤ ω} = Set.Icc 0 (laborForce σ χ φ C ω) := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have hL := laborForce_nonneg (σ := σ) (φ := φ) hχ hC hω
  ext s
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  refine and_congr_right fun hs => ?_
  rw [← Real.rpow_le_rpow_iff hs hL hφ, laborForce_rpow hχ hC hω hφ, le_div_iff₀ hk, mul_comm]

/-- Galí (2015), pp. 201, 204: within the unit interval of members, the participating
members of type `j` are exactly `[0, min L 1]`. -/
theorem participation_set_unit {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) :
    {s ∈ Set.Icc (0 : ℝ) 1 | χ * C ^ σ * s ^ φ ≤ ω} = Set.Icc 0 (min (laborForce σ χ φ C ω) 1) := by
  have h := participation_set_eq (σ := σ) hχ hC hω hφ
  ext s
  have hs := Set.ext_iff.mp h s
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, le_min_iff] at hs ⊢
  constructor
  · rintro ⟨⟨h0, h1⟩, hd⟩
    exact ⟨h0, (hs.mp ⟨h0, hd⟩).2, h1⟩
  · rintro ⟨h0, hL, h1⟩
    exact ⟨⟨h0, h1⟩, (hs.mpr ⟨h0, hL⟩).2⟩

/-- Galí (2015), eq. (5), p. 204: the marginal participant `L` is indifferent, i.e. its
disutility in consumption units equals the real wage, `χ C^σ L^φ = ω`. -/
theorem marginal_indifferent {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) : χ * C ^ σ * laborForce σ χ φ C ω ^ φ = ω :=
  ((eq5_iff hχ hC hω hφ (laborForce_nonneg hχ hC hω)).mpr rfl).symm

/-- Galí (2015), p. 204: members below the marginal participant, `0 ≤ s < L`, strictly gain
from working: `χ C^σ s^φ < ω`. -/
theorem inframarginal_strict {σ χ φ C ω s : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) (hs : 0 ≤ s) (hsL : s < laborForce σ χ φ C ω) : χ * C ^ σ * s ^ φ < ω := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have h := (Real.rpow_lt_rpow_iff hs (laborForce_nonneg hχ hC hω) hφ).mpr hsL
  rw [laborForce_rpow hχ hC hω hφ, lt_div_iff₀ hk] at h
  linarith

/-- Galí (2015), p. 204: members above the marginal participant, `s > L`, strictly lose
from working: `χ C^σ s^φ > ω`, so they stay out of the labour force. -/
theorem supramarginal_refuses {σ χ φ C ω s : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) (hsL : laborForce σ χ φ C ω < s) : ω < χ * C ^ σ * s ^ φ := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have hL := laborForce_nonneg (σ := σ) (φ := φ) hχ hC hω
  have h := (Real.rpow_lt_rpow_iff hL (by linarith) hφ).mpr hsL
  rw [laborForce_rpow hχ hC hω hφ, div_lt_iff₀ hk] at h
  linarith

/-- Galí (2015), pp. 201, 204: the marginal participant lies in the unit interval of members,
`L ≤ 1`, iff the real wage does not exceed the disutility of the member `s = 1`,
`ω ≤ χ C^σ`. -/
theorem laborForce_le_one_iff {σ χ φ C ω : ℝ} (hχ : 0 < χ) (hC : 0 < C) (hω : 0 ≤ ω)
    (hφ : 0 < φ) : laborForce σ χ φ C ω ≤ 1 ↔ ω ≤ χ * C ^ σ := by
  have hk : 0 < χ * C ^ σ := mul_pos hχ (Real.rpow_pos_of_pos hC σ)
  have hL := laborForce_nonneg (σ := σ) (φ := φ) hχ hC hω
  rw [← Real.rpow_le_rpow_iff hL zero_le_one hφ, laborForce_rpow hχ hC hω hφ, Real.one_rpow,
    div_le_one hk]

end Gali.Unemployment.IndivisibleLabor
