/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Expectations
import Mathlib.Algebra.Ring.GeomSum

/-!
# The dynamic IS equation

Galí (2015), Chapter 3, §3.3, pp. 58 and 63. Combining the consumer's Euler
equation with goods-market clearing `Y_t = C_t` gives the Euler equation in
output, eq. (13),

  `y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`.

## Main results

* `forward_sum`: iterating any forward equation `x_t = E_t x_{t+1} + f_t`
  gives the exact finite-horizon identity
  `x_t = ∑_{k<T} E_t f_{t+k} + E_t x_{t+T}`.
* `euler_forward_finite`, `euler_forward_ar1`: the forward iteration of (13)
  (p. 58); for an AR(1) preference shock the shock term is
  `σ⁻¹ (1 − ρ_zᵀ) z_t`.
* `euler_forward_tendsto`, `euler_forward_tsum`: the infinite-horizon form of
  p. 58, `y_t = σ⁻¹ z_t − σ⁻¹ ∑_k E_t (r_{t+k} − ρ) + lim_T E_t y_{t+T}`; the
  series of expected real-rate gaps converges whenever `E_t y_{t+T}` does.
* `natRate_iff`: the natural rate `r^n_t` is the only real rate at which
  output equals its natural level in (13).
* `natRate_ar1`: eq. (24), `r^n_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`.
* `euler_iff_disGap`: eq. (13) is equivalent to the DIS in gaps, eq. (23).
* `gap_forward_tendsto`, `gap_forward_tsum`: eq. (25),
  `ỹ_t = −σ⁻¹ ∑_k E_t (r_{t+k} − r^n_{t+k})` when `E_t ỹ_{t+T} → 0`.
-/

namespace Gali.BasicNewKeynesianModel.DIS

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), p. 63: the (expected) real interest rate
`r_t ≡ i_t − E_t π_{t+1}`. -/
def realRate (i infl : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => i t - 𝔼.E t (infl (t + 1))

/-- Galí (2015), eq. (13), p. 58: the Euler equation in output,
`y_t = E_t y_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t`. -/
def EulerOutput (σ ρ ρz : ℝ) (y i infl z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), eq. (20), p. 62: the elasticity of natural output with
respect to technology, `ψ_ya = (1 + φ)/(σ (1 − α) + φ + α)`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), eq. (20), p. 62: natural output `y^n_t = ψ_ya a_t + ψ_y`. -/
def natOutput (ψya ψy : ℝ) (a : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => ψya • a t + fun _ => ψy

/-- Galí (2015), p. 63: the natural rate of interest, the real rate that
supports the natural level of output in (13),
`r^n_t = ρ + σ (E_t y^n_{t+1} − y^n_t) + (1 − ρ_z) z_t`. -/
def natRate (σ ρ ρz : ℝ) (yn z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => ρ) + σ • (𝔼.E t (yn (t + 1)) - yn t) + (1 - ρz) • z t

/-- Galí (2015), eq. (23), p. 63: the dynamic IS equation in terms of the
output gap, `ỹ_t = −σ⁻¹ (i_t − E_t π_{t+1} − r^n_t) + E_t ỹ_{t+1}`. -/
def DISGap (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = -σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) + 𝔼.E t (ygap (t + 1))

/-- Galí (2015), p. 58 (the forward solution of (13)): an adapted solution of
`x_t = E_t x_{t+1} + f_t` satisfies, for every horizon `T`, the exact identity
`x_t = ∑_{k<T} E_t f_{t+k} + E_t x_{t+T}`. -/
theorem forward_sum {x f : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (h : ∀ t, x t = 𝔼.E t (x (t + 1)) + f t) (t T : ℕ) :
    x t = ∑ k ∈ Finset.range T, 𝔼.E t (f (t + k)) + 𝔼.E t (x (t + T)) := by
  induction T with
  | zero => simp [hx t]
  | succ T ih =>
    rw [ih, h (t + T), map_add, 𝔼.tower (Nat.le_add_right t T), Finset.sum_range_succ,
      ← add_assoc t T 1]
    abel

/-- Galí (2015), p. 58: the forward iteration of (13) over a finite horizon
`T`, an exact identity:
`y_t = ∑_{k<T} σ⁻¹ (1 − ρ_z) E_t z_{t+k} − σ⁻¹ ∑_{k<T} E_t (r_{t+k} − ρ) + E_t y_{t+T}`. -/
theorem euler_forward_finite {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hy : 𝔼.Adapted y)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t T : ℕ) :
    y t = ∑ k ∈ Finset.range T, (σ⁻¹ * (1 - ρz)) • 𝔼.E t (z (t + k))
      - σ⁻¹ • ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
      + 𝔼.E t (y (t + T)) := by
  have hf : ∀ s, y s = 𝔼.E s (y (s + 1))
      + ((σ⁻¹ * (1 - ρz)) • z s - σ⁻¹ • (realRate 𝔼 i infl s - fun _ => ρ)) := by
    intro s
    rw [h s, realRate]
    abel
  rw [forward_sum 𝔼 hy hf t T]
  simp only [map_sub, map_smul, Finset.sum_sub_distrib, smul_sub, Finset.smul_sum]

/-- Galí (2015), p. 58: for an AR(1) preference shock (`E_t z_{t+1} = ρ_z z_t`)
the forward iteration of (13) over `T` periods reads
`y_t = σ⁻¹ (1 − ρ_zᵀ) z_t − σ⁻¹ ∑_{k<T} E_t (r_{t+k} − ρ) + E_t y_{t+T}`. -/
theorem euler_forward_ar1 {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hy : 𝔼.Adapted y)
    (hz : 𝔼.IsAR1 ρz z) (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t T : ℕ) :
    y t = (σ⁻¹ * (1 - ρz ^ T)) • z t
      - σ⁻¹ • ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
      + 𝔼.E t (y (t + T)) := by
  rw [euler_forward_finite 𝔼 hy h t T]
  congr 2
  simp only [𝔼.ar1_iterate hz, smul_smul, ← Finset.sum_smul]
  have hg : (1 - ρz) * ∑ k ∈ Finset.range T, ρz ^ k = 1 - ρz ^ T := by
    linear_combination -(geom_sum_mul ρz T)
  rw [← Finset.mul_sum, mul_assoc, hg]

/-- Galí (2015), p. 58: if `E_t y_{t+T}` converges to `L` as `T → ∞` and
`|ρ_z| < 1`, the partial sums of expected real-rate gaps converge, with
`∑_{k<T} E_t (r_{t+k} − ρ) → z_t − σ (y_t − L)`. -/
theorem euler_forward_tendsto {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hρz : |ρz| < 1) (hy : 𝔼.Adapted y) (hz : 𝔼.IsAR1 ρz z)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t : ℕ) {L : Ω → ℝ}
    (hlim : Tendsto (fun T => 𝔼.E t (y (t + T))) atTop (𝓝 L)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ))
      atTop (𝓝 (z t - σ • (y t - L))) := by
  have hid : ∀ T, ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
      = (1 - ρz ^ T) • z t - σ • (y t - 𝔼.E t (y (t + T))) := by
    intro T
    have e := euler_forward_ar1 𝔼 hy hz h t T
    set S := ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp at e'
    linear_combination e'
  have hp : Tendsto (fun T : ℕ => (1 : ℝ) - ρz ^ T) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρz)
  have hlim' := (hp.smul_const (z t)).sub
    (((tendsto_const_nhds (x := y t)).sub hlim).const_smul σ)
  rw [one_smul] at hlim'
  exact hlim'.congr fun T => (hid T).symm

/-- Galí (2015), p. 58: the infinite-horizon forward solution of (13),
`y_t = σ⁻¹ z_t − σ⁻¹ ∑_{k ≥ 0} E_t (r_{t+k} − ρ) + lim_T E_t y_{t+T}`, for a
summable series of expected real-rate gaps. -/
theorem euler_forward_tsum {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hρz : |ρz| < 1) (hy : 𝔼.Adapted y) (hz : 𝔼.IsAR1 ρz z)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t : ℕ) {L : Ω → ℝ}
    (hlim : Tendsto (fun T => 𝔼.E t (y (t + T))) atTop (𝓝 L))
    (hs : Summable fun k => 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)) :
    y t = σ⁻¹ • z t - σ⁻¹ • ∑' k, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ) + L := by
  have h1 := euler_forward_tendsto 𝔼 hσ hρz hy hz h t hlim
  rw [tendsto_nhds_unique hs.hasSum.tendsto_sum_nat h1]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), p. 58: the forward solution of (13) under
`lim_T E_t y_{t+T} = 0`: `y_t = σ⁻¹ z_t − σ⁻¹ ∑_{k ≥ 0} E_t (r_{t+k} − ρ)`, and
the partial sums converge to `z_t − σ y_t`. -/
theorem euler_forward_limit_zero {σ ρ ρz : ℝ} {y i infl z : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hρz : |ρz| < 1) (hy : 𝔼.Adapted y) (hz : 𝔼.IsAR1 ρz z)
    (h : EulerOutput 𝔼 σ ρ ρz y i infl z) (t : ℕ)
    (hlim : Tendsto (fun T => 𝔼.E t (y (t + T))) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ))
        atTop (𝓝 (z t - σ • y t)) ∧
      ((Summable fun k => 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)) →
        y t = σ⁻¹ • z t - σ⁻¹ • ∑' k, 𝔼.E t (realRate 𝔼 i infl (t + k) - fun _ => ρ)) := by
  refine ⟨by simpa using euler_forward_tendsto 𝔼 hσ hρz hy hz h t hlim, fun hs => ?_⟩
  simpa using euler_forward_tsum 𝔼 hσ hρz hy hz h t hlim hs

/-- Galí (2015), p. 63: output equals its natural level in (13) at date `t`
if and only if the real rate equals the natural rate `r^n_t`. -/
theorem natRate_iff {σ ρ ρz : ℝ} (hσ : σ ≠ 0) (yn i infl z : ℕ → Ω → ℝ) (t : ℕ) :
    (yn t = 𝔼.E t (yn (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
        + (σ⁻¹ * (1 - ρz)) • z t) ↔ realRate 𝔼 i infl t = natRate 𝔼 σ ρ ρz yn z t := by
  unfold realRate natRate
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp
    linear_combination e

/-- Galí (2015), eq. (24), p. 63: when technology follows an AR(1) process with
persistence `ρ_a` and natural output is `y^n_t = ψ_ya a_t + ψ_y`, the natural
rate is `r^n_t = ρ − σ (1 − ρ_a) ψ_ya a_t + (1 − ρ_z) z_t`. -/
theorem natRate_ar1 {σ ρ ρz ρa ψya ψy : ℝ} {a : ℕ → Ω → ℝ} (ha : 𝔼.IsAR1 ρa a)
    (z : ℕ → Ω → ℝ) (t : ℕ) :
    natRate 𝔼 σ ρ ρz (natOutput ψya ψy a) z t
      = (fun _ => ρ) - (σ * (1 - ρa) * ψya) • a t + (1 - ρz) • z t := by
  unfold natRate natOutput
  rw [map_add, map_smul, 𝔼.const, ha.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (23), p. 63: with the output gap `ỹ_t = y_t − y^n_t` and
the natural rate `r^n`, the Euler equation (13) is equivalent to the DIS
equation in gaps. -/
theorem euler_iff_disGap {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {y yn ygap i infl z : ℕ → Ω → ℝ}
    (hgap : ∀ t, ygap t = y t - yn t) :
    EulerOutput 𝔼 σ ρ ρz y i infl z ↔ DISGap 𝔼 σ ygap i infl (natRate 𝔼 σ ρ ρz yn z) := by
  unfold EulerOutput DISGap natRate
  simp only [hgap, map_sub]
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp at e ⊢
    linear_combination e

/-- Galí (2015), eq. (25), p. 63: if `E_t ỹ_{t+T} → 0`, the partial sums of
expected real-rate gaps `∑_{k<T} E_t (r_{t+k} − r^n_{t+k})` converge to
`−σ ỹ_t`. -/
theorem gap_forward_tendsto {σ : ℝ} {ygap i infl rn : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hy : 𝔼.Adapted ygap) (h : DISGap 𝔼 σ ygap i infl rn) (t : ℕ)
    (hlim : Tendsto (fun T => 𝔼.E t (ygap (t + T))) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k)))
      atTop (𝓝 (-σ • ygap t)) := by
  have hf : ∀ s, ygap s = 𝔼.E s (ygap (s + 1)) + (-σ⁻¹) • (realRate 𝔼 i infl s - rn s) := by
    intro s
    rw [h s, realRate, neg_smul]
    abel
  have hid : ∀ T, ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k))
      = -σ • (ygap t - 𝔼.E t (ygap (t + T))) := by
    intro T
    have e := forward_sum 𝔼 hy hf t T
    simp only [map_smul, ← Finset.smul_sum] at e
    set S := ∑ k ∈ Finset.range T, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k))
    funext ω
    have e' := congrFun e ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e' ⊢
    field_simp at e'
    linear_combination e'
  have hlim' := ((tendsto_const_nhds (x := ygap t)).sub hlim).const_smul (-σ)
  rw [sub_zero] at hlim'
  exact hlim'.congr fun T => (hid T).symm

/-- Galí (2015), eq. (25), p. 63: under `lim_T E_t ỹ_{t+T} = 0`, and for a
summable series, `ỹ_t = −σ⁻¹ ∑_{k ≥ 0} E_t (r_{t+k} − r^n_{t+k})`. -/
theorem gap_forward_tsum {σ : ℝ} {ygap i infl rn : ℕ → Ω → ℝ} (hσ : σ ≠ 0)
    (hy : 𝔼.Adapted ygap) (h : DISGap 𝔼 σ ygap i infl rn) (t : ℕ)
    (hlim : Tendsto (fun T => 𝔼.E t (ygap (t + T))) atTop (𝓝 0))
    (hs : Summable fun k => 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k))) :
    ygap t = -σ⁻¹ • ∑' k, 𝔼.E t (realRate 𝔼 i infl (t + k) - rn (t + k)) := by
  rw [tendsto_nhds_unique hs.hasSum.tendsto_sum_nat (gap_forward_tendsto 𝔼 hσ hy h t hlim)]
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

end Gali.BasicNewKeynesianModel.DIS
