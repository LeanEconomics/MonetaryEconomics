/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations

/-!
# Exercise 3.9: the hybrid Phillips curve of Galí and Gertler

Galí (2015), Chapter 3, Exercise 3.9, pp. 96–97 (Galí and Gertler 1999). A
fraction `ω` of price setters follows the backward-looking rule
`p^b_t = p*_{t−1} + π_{t−1}`; the rest set `p^f_t` as in the standard model
(`α = 0`). The average new price is `p*_t = ω p^b_t + (1 − ω) p^f_t`, the price
level is `p_t = θ p_{t−1} + (1 − θ) p*_t`, and `μ̂_t = −(σ + φ) ỹ_t`.

* `forward_price_recursive`: the forward-looking price
  `p^f_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}` satisfies
  `p^f_t = (1 − βθ)(μ + ψ_t) + βθ E_t p^f_{t+1}` (for bounded marginal cost).
* (a) `hybrid_nkpc`: `π_t = γ_b π_{t−1} + γ_f E_t π_{t+1} + κ ỹ_t` with
  `γ_b = ω/φ̃`, `γ_f = βθ/φ̃`, `κ = (1 − ω)(1 − θ)(1 − βθ)(σ + φ)/φ̃`,
  `φ̃ = θ + ω(1 − θ(1 − β))`; `hybrid_nkpc_of_series` starts from the series
  form of `p^f`. `hybrid_standard`: `ω = 0` gives the standard NKPC;
  `gammas_sum`: `γ_b + γ_f = 1 − θ(1 − β)(1 − ω)/φ̃ ≤ 1`.
* (b) is a discussion of disinflation costs; it is not formalised.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_9

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Coefficients -/

/-- `φ̃ = θ + ω(1 − θ(1 − β))` (Galí (2015), Ex. 3.9(a), p. 97). -/
def phiTilde (β θ ω : ℝ) : ℝ := θ + ω * (1 - θ * (1 - β))

/-- The backward-looking coefficient `γ_b = ω/φ̃` (Galí (2015), Ex. 3.9(a)). -/
noncomputable def gammaB (β θ ω : ℝ) : ℝ := ω / phiTilde β θ ω

/-- The forward-looking coefficient `γ_f = βθ/φ̃` (Galí (2015), Ex. 3.9(a)). -/
noncomputable def gammaF (β θ ω : ℝ) : ℝ := β * θ / phiTilde β θ ω

/-- The slope `κ = (1 − ω)(1 − θ)(1 − βθ)(σ + φ)/φ̃` (Galí (2015), Ex. 3.9(a)). -/
noncomputable def kappaH (β θ ω σ φ : ℝ) : ℝ :=
  (1 - ω) * (1 - θ) * (1 - β * θ) * (σ + φ) / phiTilde β θ ω

/-- `φ̃ ≥ θ > 0` for `θ ∈ (0,1)`, `β ≥ 0`, `ω ≥ 0` (Galí (2015), Ex. 3.9(a)). -/
theorem phiTilde_pos {β θ ω : ℝ} (hβ0 : 0 ≤ β) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hω0 : 0 ≤ ω) : 0 < phiTilde β θ ω := by
  unfold phiTilde
  have : 0 < 1 - θ * (1 - β) := by nlinarith
  positivity

/-! ### The forward-looking price as a recursion -/

/-- A geometrically weighted series of uniformly bounded random variables
converges (Galí (2015), Ex. 3.9, p. 97). -/
theorem summable_geometric_bounded {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (ω : Ω) : Summable fun k => a ^ k * y k ω := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy k ω) (pow_nonneg (abs_nonneg a) k)

/-- **`E_t` commutes with discounted sums of bounded random variables**
(Galí (2015), Ex. 3.9, p. 97; a local copy of the interchange used for eq. (11)):
`E_t[∑ₖ aᵏ yₖ] = ∑ₖ aᵏ E_t yₖ` for `|a| < 1`. `E_t` is monotone and preserves
constants, hence continuous for the uniform norm. -/
theorem E_tsum {a : ℝ} (ha : |a| < 1) {y : ℕ → Ω → ℝ} {M : ℝ}
    (hy : ∀ k ω, |y k ω| ≤ M) (t : ℕ) :
    𝔼.E t (fun ω => ∑' k, a ^ k * y k ω) = fun ω => ∑' k, a ^ k * 𝔼.E t (y k) ω := by
  funext ω
  set F : Ω → ℝ := fun ω => ∑' k, a ^ k * y k ω with hF
  set Fn : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range n, a ^ k • y k with hFn
  set T : ℕ → ℝ := fun n => ∑' k, |a| ^ (k + n) * M with hT
  have hTlim : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add fun k => |a| ^ k * M
  have htail : ∀ n ω', |F ω' - Fn n ω'| ≤ T n := by
    intro n ω'
    have hs := summable_geometric_bounded ha hy ω'
    have hsplit := hs.sum_add_tsum_nat_add n
    have hFn' : Fn n ω' = ∑ k ∈ Finset.range n, a ^ k * y k ω' := by
      simp [hFn, Finset.sum_apply]
    rw [hFn']
    change |∑' k, a ^ k * y k ω' - _| ≤ T n
    rw [← hsplit, add_sub_cancel_left]
    have hs' : Summable fun k => a ^ (k + n) * y (k + n) ω' :=
      (summable_nat_add_iff n).mpr hs
    have hg : Summable fun k => |a| ^ (k + n) * M :=
      (summable_nat_add_iff n).mpr
        ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    calc |∑' k, a ^ (k + n) * y (k + n) ω'| ≤ ∑' k, |a ^ (k + n) * y (k + n) ω'| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun k => a ^ (k + n) * y (k + n) ω')
              (by simpa only [Real.norm_eq_abs] using hs'.abs)
      _ ≤ T n := by
          refine Summable.tsum_le_tsum (fun k => ?_) hs'.abs hg
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (hy (k + n) ω') (pow_nonneg (abs_nonneg a) _)
  have hEFn : ∀ n, 𝔼.E t (Fn n) ω = ∑ k ∈ Finset.range n, a ^ k * 𝔼.E t (y k) ω := by
    intro n
    simp [hFn, map_sum, map_smul, Finset.sum_apply]
  have hlim1 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop (𝓝 (𝔼.E t F ω)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hTlim
    have h := 𝔼.abs_E_le (x := F - Fn n) (fun ω' => htail n ω') t ω
    rw [map_sub, Pi.sub_apply] at h
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact h
  have hbE : ∀ k ω', |𝔼.E t (y k) ω'| ≤ M := fun k ω' => 𝔼.abs_E_le (hy k) t ω'
  have hlim2 : Tendsto (fun n => 𝔼.E t (Fn n) ω) atTop
      (𝓝 (∑' k, a ^ k * 𝔼.E t (y k) ω)) := by
    simp_rw [hEFn]
    exact (summable_geometric_bounded ha hbE ω).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hlim1 hlim2

/-- **The forward-looking price in recursive form** (Galí (2015), Ex. 3.9, p. 97,
and eq. (16), p. 60). If `p^f_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}` with `ψ`
adapted and uniformly bounded and `0 ≤ βθ < 1`, then
`p^f_t = (1 − βθ)(μ + ψ_t) + βθ E_t p^f_{t+1}`. -/
theorem forward_price_recursive {β θ μ : ℝ} (hb0 : 0 ≤ β * θ) (hb1 : β * θ < 1)
    {ψ pf : ℕ → Ω → ℝ} {M : ℝ} (hψ : ∀ t ω, |ψ t ω| ≤ M) (hψa : 𝔼.Adapted ψ)
    (hpf : ∀ t ω, pf t ω = μ + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + k)) ω)
    (t : ℕ) : pf t = (1 - β * θ) • ((fun _ => μ) + ψ t) + (β * θ) • 𝔼.E t (pf (t + 1)) := by
  have ha : |β * θ| < 1 := by rwa [abs_of_nonneg hb0]
  have hy : ∀ k ω, |𝔼.E (t + 1) (ψ (t + 1 + k)) ω| ≤ M :=
    fun k ω => 𝔼.bounded_E hψ (t + 1) (t + 1 + k) ω
  have hpf' : pf (t + 1) = (fun _ => μ) + (1 - β * θ) •
      fun ω => ∑' k, (β * θ) ^ k * 𝔼.E (t + 1) (ψ (t + 1 + k)) ω := by
    funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hpf (t + 1) ω]
  have hE : 𝔼.E t (pf (t + 1)) = (fun _ => μ) + (1 - β * θ) •
      fun ω => ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + 1 + k)) ω := by
    rw [hpf', map_add, map_smul, 𝔼.const, E_tsum 𝔼 ha hy t]
    congr 2
    funext ω
    congr 1
    funext k
    rw [𝔼.tower (Nat.le_succ t)]
  rw [hE]
  funext ω
  have hs := summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hψ t (t + k) ω') ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hpf t ω, hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, hψa t]
  have : ∑' k, (β * θ) ^ (k + 1) * 𝔼.E t (ψ (t + (k + 1))) ω
      = (β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + 1 + k)) ω := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [pow_succ, show t + (k + 1) = t + 1 + k by omega]
    ring
  rw [this]
  ring

/-! ### (a) The hybrid New Keynesian Phillips curve -/

/-- **The hybrid NKPC** (Galí (2015), Ex. 3.9(a), p. 97). Suppose, for all
dates, the backward-looking rule `p^b_{t+1} = p*_t + π_t`, the average new price
`p*_t = ω p^b_t + (1 − ω) p^f_t`, the forward-looking price in recursive form
`p^f_t = (1 − βθ)(μ + ψ_t) + βθ E_t p^f_{t+1}`, the price level
`p_{t+1} = θ p_t + (1 − θ) p*_{t+1}`, `π_{t+1} = p_{t+1} − p_t`, the markup
`μ_t = p_t − ψ_t` with `μ̂_t = μ_t − μ = −(σ + φ) ỹ_t`, and `p`, `p*` adapted.
Then from the third date on
`π_t = γ_b π_{t−1} + γ_f E_t π_{t+1} + κ ỹ_t`. -/
theorem hybrid_nkpc {β θ ω σ φ μ : ℝ} (hβ0 : 0 ≤ β) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hω0 : 0 ≤ ω) {p pstar pb pf ψ muhat ytil infl : ℕ → Ω → ℝ}
    (hpb : ∀ t, pb (t + 1) = pstar t + infl t)
    (hstar : ∀ t, pstar t = ω • pb t + (1 - ω) • pf t)
    (hpf : ∀ t, pf t = (1 - β * θ) • ((fun _ => μ) + ψ t) + (β * θ) • 𝔼.E t (pf (t + 1)))
    (hp : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hmu : ∀ t, muhat t = (p t - ψ t) - fun _ => μ)
    (hmuy : ∀ t, muhat t = -(σ + φ) • ytil t)
    (hpa : 𝔼.Adapted p) (hsa : 𝔼.Adapted pstar) (t : ℕ) :
    infl (t + 2) = gammaB β θ ω • infl (t + 1) + gammaF β θ ω • 𝔼.E (t + 2) (infl (t + 3))
      + kappaH β θ ω σ φ • ytil (t + 2) := by
  -- expectations of next-period variables
  have hEp : 𝔼.E (t + 2) (p (t + 3))
      = θ • p (t + 2) + (1 - θ) • 𝔼.E (t + 2) (pstar (t + 3)) := by
    rw [hp (t + 2), map_add, map_smul, map_smul, hpa (t + 2)]
  have hEs : 𝔼.E (t + 2) (pstar (t + 3))
      = ω • 𝔼.E (t + 2) (pb (t + 3)) + (1 - ω) • 𝔼.E (t + 2) (pf (t + 3)) := by
    rw [hstar (t + 3), map_add, map_smul, map_smul]
  have hEb : 𝔼.E (t + 2) (pb (t + 3)) = pstar (t + 2) + (p (t + 2) - p (t + 1)) := by
    have hk : 𝔼.E (t + 2) (p (t + 1)) = p (t + 1) := by
      rw [← hpa (t + 1), 𝔼.known (by omega)]
    rw [hpb (t + 2), hinfl (t + 1), map_add, map_sub, hsa (t + 2), hpa (t + 2), hk]
  have hEi : 𝔼.E (t + 2) (infl (t + 3)) = 𝔼.E (t + 2) (p (t + 3)) - p (t + 2) := by
    rw [hinfl (t + 2), map_sub, hpa (t + 2)]
  funext x
  have e1 := congrFun (hp t) x
  have e2 := congrFun (hp (t + 1)) x
  have e3 := congrFun (hpb (t + 1)) x
  have e3' := congrFun (hinfl t) x
  have e4 := congrFun (hstar (t + 2)) x
  have e5 := congrFun (hpf (t + 2)) x
  have e6 := congrFun (hmu (t + 2)) x
  have e7 := congrFun (hmuy (t + 2)) x
  have e8 := congrFun hEp x
  have e9 := congrFun hEs x
  have e10 := congrFun hEb x
  have e11 := congrFun hEi x
  have e12 := congrFun (hinfl (t + 1)) x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
    at e1 e2 e3 e3' e4 e5 e6 e7 e8 e9 e10 e11 e12 ⊢
  -- name the scalars
  set pm2 := p t x
  set pm1 := p (t + 1) x
  set p0 := p (t + 2) x
  set sm1 := pstar (t + 1) x
  set s0 := pstar (t + 2) x
  set b0 := pb (t + 2) x
  set f0 := pf (t + 2) x
  set Ef := 𝔼.E (t + 2) (pf (t + 3)) x
  set Eπ := 𝔼.E (t + 2) (infl (t + 3)) x
  set y0 := ytil (t + 2) x
  set πm1 := infl (t + 1) x
  set π0 := infl (t + 2) x
  -- the steps of the derivation
  have a1 : (1 - θ) * (sm1 - pm2) = πm1 := by linear_combination -e1 - e3'
  have a2 : (1 - θ) * (s0 - pm1) = π0 := by linear_combination -e2 - e12
  have a3 : (1 - θ) * (b0 - pm1) = πm1 := by linear_combination (1 - θ) * e3 + a1 + (1 - θ) * e3'
  have a4 : (1 - θ) * (𝔼.E (t + 2) (pb (t + 3)) x - p0) = π0 := by
    linear_combination (1 - θ) * e10 + a2
  have a5 : (1 - θ) * (𝔼.E (t + 2) (pstar (t + 3)) x - p0) = Eπ := by
    linear_combination -e8 - e11
  have hψ : ψ (t + 2) x = p0 - μ + (σ + φ) * y0 := by linear_combination e6 - e7
  have hF : f0 - pm1 = π0 + (1 - β * θ) * (σ + φ) * y0 + β * θ * (Ef - p0) := by
    linear_combination e5 + (1 - β * θ) * hψ - e12
  have g1 : π0 = ω * πm1 + (1 - ω) * (1 - θ) * (f0 - pm1) := by
    linear_combination (1 - θ) * e4 - a2 + ω * a3
  have g2 : Eπ = ω * π0 + (1 - ω) * (1 - θ) * (Ef - p0) := by
    linear_combination (1 - θ) * e9 - a5 + ω * a4
  have key : phiTilde β θ ω * π0 = ω * πm1 + β * θ * Eπ
      + (1 - ω) * (1 - θ) * (1 - β * θ) * (σ + φ) * y0 := by
    unfold phiTilde
    linear_combination g1 + (1 - ω) * (1 - θ) * hF - β * θ * g2
  have hφt := (phiTilde_pos hβ0 hθ0 hθ1 hω0).ne'
  unfold gammaB gammaF kappaH
  field_simp
  linear_combination key

/-- **The hybrid NKPC from the series form of `p^f`** (Galí (2015), Ex. 3.9(a),
p. 97): the same conclusion when `p^f_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k}`
with `ψ` adapted and uniformly bounded. -/
theorem hybrid_nkpc_of_series {β θ ω σ φ μ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hω0 : 0 ≤ ω) {p pstar pb pf ψ muhat ytil infl : ℕ → Ω → ℝ} {M : ℝ}
    (hpb : ∀ t, pb (t + 1) = pstar t + infl t)
    (hstar : ∀ t, pstar t = ω • pb t + (1 - ω) • pf t)
    (hpf : ∀ t ω', pf t ω' = μ + (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (ψ (t + k)) ω')
    (hψb : ∀ t ω', |ψ t ω'| ≤ M) (hψa : 𝔼.Adapted ψ)
    (hp : ∀ t, p (t + 1) = θ • p t + (1 - θ) • pstar (t + 1))
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t)
    (hmu : ∀ t, muhat t = (p t - ψ t) - fun _ => μ)
    (hmuy : ∀ t, muhat t = -(σ + φ) • ytil t)
    (hpa : 𝔼.Adapted p) (hsa : 𝔼.Adapted pstar) (t : ℕ) :
    infl (t + 2) = gammaB β θ ω • infl (t + 1) + gammaF β θ ω • 𝔼.E (t + 2) (infl (t + 3))
      + kappaH β θ ω σ φ • ytil (t + 2) := by
  have hb0 : 0 ≤ β * θ := mul_nonneg hβ0 hθ0.le
  have hb1 : β * θ < 1 := by nlinarith
  exact hybrid_nkpc 𝔼 hβ0 hθ0 hθ1 hω0 hpb hstar
    (fun s => forward_price_recursive 𝔼 hb0 hb1 hψb hψa hpf s) hp hinfl hmu hmuy hpa hsa t

/-- **No backward-looking firms: the standard NKPC** (Galí (2015), Ex. 3.9(a),
and eq. (22), p. 63, with `α = 0`): at `ω = 0`, `γ_b = 0`, `γ_f = β` and
`κ = (1 − θ)(1 − βθ)(σ + φ)/θ`. -/
theorem hybrid_standard {β θ σ φ : ℝ} (hθ0 : 0 < θ) :
    gammaB β θ 0 = 0 ∧ gammaF β θ 0 = β ∧
      kappaH β θ 0 σ φ = (1 - θ) * (1 - β * θ) * (σ + φ) / θ := by
  unfold gammaB gammaF kappaH phiTilde
  refine ⟨by simp, ?_, by simp⟩
  simp only [zero_mul, add_zero]
  field_simp

/-- **`γ_b + γ_f ≤ 1`** (Galí (2015), Ex. 3.9(a)): exactly,
`γ_b + γ_f = 1 − θ(1 − β)(1 − ω)/φ̃`, since `φ̃ − ω − βθ = θ(1 − β)(1 − ω)`. -/
theorem gammas_sum {β θ ω : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    gammaB β θ ω + gammaF β θ ω = 1 - θ * (1 - β) * (1 - ω) / phiTilde β θ ω ∧
      gammaB β θ ω + gammaF β θ ω ≤ 1 := by
  have hφ := phiTilde_pos hβ0 hθ0 hθ1 hω0
  have heq : gammaB β θ ω + gammaF β θ ω = 1 - θ * (1 - β) * (1 - ω) / phiTilde β θ ω := by
    unfold gammaB gammaF
    field_simp
    unfold phiTilde
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have : 0 ≤ θ * (1 - β) * (1 - ω) / phiTilde β θ ω := by
    apply div_nonneg _ hφ.le
    apply mul_nonneg (mul_nonneg hθ0.le (by linarith)) (by linarith)
  linarith

end Gali.BasicNewKeynesianModel.Ex3_9
