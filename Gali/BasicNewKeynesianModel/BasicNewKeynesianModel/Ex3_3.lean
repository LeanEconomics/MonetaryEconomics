/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Ex3_2
import BasicNewKeynesianModel.CES

/-!
# Exercise 3.3: government purchases and sticky prices

Galí (2015), Chapter 3, Exercise 3.3 (pp. 89–91). The government buys a fraction `τ_t` of the
output of every good, `G_t(i) = τ_t Y_t(i)`, financed by lump-sum taxes; `g_t ≡ −log(1 − τ_t)`.
Households: Euler equation `c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)` and labour supply
`w_t − p_t = σ c_t + φ n_t`; technology `y_t = n_t`; the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`;
under flexible prices firms set a constant (log) markup `μ` over marginal cost.

## Main results

* (a) `cesAgg_smul`, `goods_market_exact`: `C(i) = (1 − τ) Y(i)` gives `C = (1 − τ) Y` for the CES
  indices, hence `y_t = c_t + g_t` **exactly**.
* (b) `natural_output`, `natural_output_iff`: `y^n = (σ g − μ)/(σ + φ)`;
  `natOutput_multiplier_mem`, `natCons_multiplier_neg`: under flexible prices a fiscal expansion
  raises output by a fraction `σ/(σ + φ) ∈ (0, 1)` of `g` and lowers consumption: the negative
  wealth effect raises labour supply at the unchanged real wage `−μ`.
* (c) `euler_iff_dis_output`, `dis_output_iff_gap`, `euler_iff_dis_gap`: the DIS
  `ỹ_t = E_t ỹ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r^n_t)` with
  `r^n_t = ρ + σφ/(σ + φ)(g_t − E_t g_{t+1})`; `natRate_eq_euler` (the rate that supports the
  natural allocation); `natRate_ar1`: `r^n_t = ρ + σφ(1 − ρ_g)/(σ + φ) g_t`.
* (d) Under `i_t = ρ + φ_π π_t`: `schurStable_iff` (determinacy iff `φ_π > 1`),
  `msv_equilibrium` (existence), `equilibrium_iff_msv` (the MSV solution
  `ỹ_t = (1 − βρ_g) Λ_g c_g g_t`, `π_t = κ Λ_g c_g g_t` is the unique bounded equilibrium),
  `equilibrium_not_unique` (indeterminacy for `φ_π ≤ 1`), and the responses
  `msv_responses_pos`, `output_multiplier_bounds`: gap, inflation and the nominal rate rise,
  and the output multiplier lies strictly between its flexible-price value `σ/(σ + φ)` and one.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_3

open MeasureTheory Gali.BasicNewKeynesianModel.CES

/-! ### (a) Goods-market clearing -/

namespace Goods

variable {Gd : Type*} [MeasurableSpace Gd] {μ : Measure Gd} {ε : ℝ}

/-- Galí (2015), Ex. 3.3(a), p. 90: the CES index is homogeneous of degree one,
`(∫ (k c(i))^r)^{1/r} = k (∫ c(i)^r)^{1/r}` for `k ≥ 0`. -/
theorem cesAgg_smul (hε : 1 < ε) {k : ℝ} (hk : 0 ≤ k) {c : Gd → ℝ} (hc : ∀ i, 0 ≤ c i) :
    cesAgg μ ε (fun i => k * c i) = k * cesAgg μ ε c := by
  have hε0 : (0 : ℝ) < ε := by linarith
  have hr : (ε - 1) / ε ≠ 0 := div_ne_zero (by linarith) hε0.ne'
  unfold cesAgg
  simp_rw [Real.mul_rpow hk (hc _)]
  rw [integral_const_mul, Real.mul_rpow (Real.rpow_nonneg hk _)
    (integral_nonneg fun i => Real.rpow_nonneg (hc i) _), Real.rpow_rpow_inv hk hr]

/-- Galí (2015), Ex. 3.3(a), p. 90: **exact goods-market clearing**. If the government buys
`G(i) = τ Y(i)` of every good and households consume the rest, `C(i) = Y(i) − τ Y(i)`, then
the indices satisfy `C = (1 − τ) Y` and `G = τ Y`; so with `g ≡ −log(1 − τ)`,
`y = c + g` holds exactly (not only to first order). -/
theorem goods_market_exact (hε : 1 < ε) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) {Y : Gd → ℝ}
    (hY : ∀ i, 0 ≤ Y i) (hYpos : 0 < cesAgg μ ε Y) :
    cesAgg μ ε (fun i => Y i - τ * Y i) = (1 - τ) * cesAgg μ ε Y ∧
      cesAgg μ ε (fun i => τ * Y i) = τ * cesAgg μ ε Y ∧
      Real.log (cesAgg μ ε Y) =
        Real.log (cesAgg μ ε (fun i => Y i - τ * Y i)) + -Real.log (1 - τ) := by
  have hC : cesAgg μ ε (fun i => Y i - τ * Y i) = (1 - τ) * cesAgg μ ε Y := by
    rw [← cesAgg_smul hε (by linarith) hY]
    congr 1
    funext i
    ring
  refine ⟨hC, cesAgg_smul hε hτ0 hY, ?_⟩
  rw [hC, Real.log_mul (by linarith) hYpos.ne']
  ring

end Goods

/-! ### (b) The natural level of output -/

/-- Galí (2015), Ex. 3.3(b), p. 90: **natural output**. Under flexible prices the real wage
equals the inverse markup, `w − p = −μ` (price = markup over nominal marginal cost `w`, since
`y = n`); with labour supply `w − p = σ c + φ n`, `y = n` and `y = c + g`, output is
`y^n = (σ g − μ)/(σ + φ)`. -/
theorem natural_output {σ φ μ y c n g wp : ℝ} (hσφ : σ + φ ≠ 0) (hmark : wp = -μ)
    (hls : wp = σ * c + φ * n) (htech : y = n) (hgm : y = c + g) :
    y = (σ * g - μ) / (σ + φ) := by
  rw [eq_div_iff hσφ]
  subst htech
  have hc : c = y - g := by linarith
  subst hc
  linarith

/-- Galí (2015), Ex. 3.3(b), p. 90: the flexible-price allocation is unique and given by
`y = n = (σ g − μ)/(σ + φ)`, `c = y − g` and `w − p = −μ`: the four conditions hold if and only
if the allocation is this one. -/
theorem natural_output_iff {σ φ μ y c n g wp : ℝ} (hσφ : σ + φ ≠ 0) :
    (wp = -μ ∧ wp = σ * c + φ * n ∧ y = n ∧ y = c + g) ↔
      (y = (σ * g - μ) / (σ + φ) ∧ n = y ∧ c = y - g ∧ wp = -μ) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨natural_output hσφ h1 h2 h3 h4, h3.symm, by linarith, h1⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h4, ?_, h2.symm, by linarith⟩
    rw [h4, h3, h2, h1]
    field_simp
    ring

/-- Galí (2015), Ex. 3.3(b), p. 90: natural consumption `c^n = y^n − g = −(φ g + μ)/(σ + φ)`. -/
theorem natural_consumption {σ φ μ g : ℝ} (hσφ : σ + φ ≠ 0) :
    (σ * g - μ) / (σ + φ) - g = -(φ * g + μ) / (σ + φ) := by
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(b), p. 90 (mechanism): for `σ, φ > 0` the flexible-price output
multiplier `σ/(σ + φ)` lies strictly between zero and one. -/
theorem natOutput_multiplier_mem {σ φ : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) :
    0 < σ / (σ + φ) ∧ σ / (σ + φ) < 1 := by
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

/-- Galí (2015), Ex. 3.3(b), p. 90 (mechanism): consumption falls one-for-`φ/(σ + φ)` with
purchases. Higher purchases make households poorer, the marginal utility of consumption
rises, and labour supply shifts out at the unchanged real wage, so employment and output
rise while consumption is crowded out. -/
theorem natCons_multiplier_neg {σ φ : ℝ} (hσ : 0 < σ) (hφ : 0 < φ) :
    σ / (σ + φ) - 1 = -(φ / (σ + φ)) ∧ -(φ / (σ + φ)) < 0 := by
  have h : σ + φ ≠ 0 := by positivity
  refine ⟨by field_simp; ring, ?_⟩
  have : 0 < φ / (σ + φ) := by positivity
  linarith

/-! ### (c) The dynamic IS equation and the natural rate -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Ex. 3.3, p. 89: the log-linear Euler equation
`c_t = E_t c_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ)`. -/
def Euler (σ ρ : ℝ) (c i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)

/-- Galí (2015), Ex. 3.3(c), p. 90: the DIS in output,
`y_t = E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ) + (g_t − E_t g_{t+1})`. -/
def DISOutput (σ ρ : ℝ) (y g i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, y t = 𝔼.E t (y (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ) +
    (g t - 𝔼.E t (g (t + 1)))

/-- Galí (2015), Ex. 3.3(b), p. 90: the natural output process `y^n_t = (σ g_t − μ)/(σ + φ)`. -/
noncomputable def natOutput (σ φ μ : ℝ) (g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σ + φ)⁻¹ • (σ • g t - fun _ => μ)

/-- Galí (2015), Ex. 3.3(c), p. 90: the natural rate
`r^n_t = ρ + (σφ/(σ + φ))(g_t − E_t g_{t+1})`. -/
noncomputable def natRate (σ φ ρ : ℝ) (g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => ρ) + (σ * φ / (σ + φ)) • (g t - 𝔼.E t (g (t + 1)))

/-- Galí (2015), Ex. 3.3(c), p. 90: the DIS in the output gap,
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r^n_t)`. -/
def DISGap (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), Ex. 3.3(c), p. 90: with `y_t = c_t + g_t`, the Euler equation holds if and
only if the output DIS holds. -/
theorem euler_iff_dis_output {σ ρ : ℝ} {y c g i infl : ℕ → Ω → ℝ}
    (hgm : ∀ t, y t = c t + g t) :
    Euler 𝔼 σ ρ c i infl ↔ DISOutput 𝔼 σ ρ y g i infl := by
  have hE : ∀ t, 𝔼.E t (y (t + 1)) = 𝔼.E t (c (t + 1)) + 𝔼.E t (g (t + 1)) :=
    fun t => by rw [hgm (t + 1), map_add]
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination h1 - h2 + h3
  · intro h t
    funext ω
    have h1 := congrFun (hgm t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination -h1 + h2 + h3

/-- Galí (2015), Ex. 3.3(c), p. 90: with `ỹ = y − y^n`, the output DIS holds if and only if
the gap DIS holds with the natural rate `r^n`. -/
theorem dis_output_iff_gap {σ φ μ ρ : ℝ} (hσ : σ ≠ 0) (hσφ : σ + φ ≠ 0)
    {y ygap g i infl : ℕ → Ω → ℝ} (hgap : ∀ t, ygap t = y t - natOutput σ φ μ g t) :
    DISOutput 𝔼 σ ρ y g i infl ↔ DISGap 𝔼 σ ygap i infl (natRate 𝔼 σ φ ρ g) := by
  have hE : ∀ t, 𝔼.E t (ygap (t + 1))
      = 𝔼.E t (y (t + 1)) - (σ + φ)⁻¹ • (σ • 𝔼.E t (g (t + 1)) - fun _ => μ) :=
    fun t => by rw [hgap (t + 1), natOutput, map_sub, map_smul, map_sub, map_smul, 𝔼.const]
  have hK : σ⁻¹ * (σ * φ / (σ + φ)) + (σ + φ)⁻¹ * σ = 1 := by
    field_simp
    ring
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (hgap t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [natOutput, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination h1 - h2 + h3 - (g t ω - 𝔼.E t (g (t + 1)) ω) * hK
  · intro h t
    funext ω
    have h1 := congrFun (hgap t) ω
    have h2 := congrFun (hE t) ω
    have h3 := congrFun (h t) ω
    simp only [natOutput, natRate, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at h1 h2 h3 ⊢
    linear_combination -h1 + h2 + h3 + (g t ω - 𝔼.E t (g (t + 1)) ω) * hK

/-- Galí (2015), Ex. 3.3(c), p. 90: **the DIS with government purchases**. Given `y = c + g`
and `ỹ = y − y^n`, the Euler equation holds if and only if
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − r^n_t)`,
`r^n_t = ρ + σφ/(σ + φ) (g_t − E_t g_{t+1})`. -/
theorem euler_iff_dis_gap {σ φ μ ρ : ℝ} (hσ : σ ≠ 0) (hσφ : σ + φ ≠ 0)
    {y c ygap g i infl : ℕ → Ω → ℝ} (hgm : ∀ t, y t = c t + g t)
    (hgap : ∀ t, ygap t = y t - natOutput σ φ μ g t) :
    Euler 𝔼 σ ρ c i infl ↔ DISGap 𝔼 σ ygap i infl (natRate 𝔼 σ φ ρ g) :=
  (euler_iff_dis_output 𝔼 hgm).trans (dis_output_iff_gap 𝔼 hσ hσφ hgap)

/-- Galí (2015), Ex. 3.3(c), p. 90: the natural rate is the real rate that supports the
natural allocation: `r^n_t = ρ + σ (E_t c^n_{t+1} − c^n_t)` with `c^n = y^n − g`. -/
theorem natRate_eq_euler {σ φ μ ρ : ℝ} (hσφ : σ + φ ≠ 0) (g : ℕ → Ω → ℝ) (t : ℕ) :
    natRate 𝔼 σ φ ρ g t = (fun _ => ρ) + σ • (𝔼.E t (natOutput σ φ μ g (t + 1) - g (t + 1)) -
      (natOutput σ φ μ g t - g t)) := by
  funext ω
  simp only [natRate, natOutput, map_sub, map_smul, 𝔼.const, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(c), p. 90: with AR(1) purchases (`E_t g_{t+1} = ρ_g g_t`) the natural
rate is `r^n_t = ρ + σφ(1 − ρ_g)/(σ + φ) g_t`. -/
theorem natRate_ar1 {σ φ ρ ρg : ℝ} {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (t : ℕ) :
    natRate 𝔼 σ φ ρ g t = (fun _ => ρ) + (σ * φ * (1 - ρg) / (σ + φ)) • g t := by
  funext ω
  simp only [natRate, hg.2 t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### (d) Equilibrium under `i_t = ρ + φ_π π_t` -/

/-- Galí (2015), Ex. 3.3, p. 90: the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), Ex. 3.3(d), p. 91: the rule `i_t = ρ + φ_π π_t`. -/
def Rule (ρ φπ : ℝ) (i infl : ℕ → Ω → ℝ) : Prop := ∀ t, i t = (fun _ => ρ) + φπ • infl t

/-- Galí (2015), Ex. 3.3(d), p. 91: an equilibrium: NKPC, gap DIS with natural rate `rn`, rule. -/
def Equilibrium (β σ κ ρ φπ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DISGap 𝔼 σ ygap i infl rn ∧ Rule ρ φπ i infl

/-- Galí (2015), Ex. 3.3(d), p. 91: the system matrix with the rate substituted out,
`A = (σ + κφ_π)⁻¹ [[σ, 1 − βφ_π], [σκ, κ + βσ]]`. -/
noncomputable def A (β σ κ φπ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![σ / (σ + κ * φπ), (1 - β * φπ) / (σ + κ * φπ);
    σ * κ / (σ + κ * φπ), (κ + β * σ) / (σ + κ * φπ)]

/-- Galí (2015), Ex. 3.3(d), p. 91: the stacked vector `(ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Galí (2015), Ex. 3.3(d), p. 91: the forcing term `(σ + κφ_π)⁻¹ (1, κ) u_t`. -/
noncomputable def forcing (σ κ φπ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(σ + κ * φπ)⁻¹ • u t, (κ / (σ + κ * φπ)) • u t]

/-- Galí (2015), Ex. 3.3(d), p. 91: with the rule substituted, the NKPC and the gap DIS hold
iff `(ỹ, π)` solves `x_t = A E_t x_{t+1} + B u_t` with `u_t = r^n_t − ρ`. -/
theorem equilibrium_iff_solves {β σ κ ρ φπ : ℝ} (hσ : σ ≠ 0) (hS : σ + κ * φπ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (hrule : Rule ρ φπ i infl) :
    Equilibrium 𝔼 β σ κ ρ φπ rn ygap infl i ↔
      𝔼.Solves (A β σ κ φπ) (forcing σ κ φπ (fun t => rn t - fun _ => ρ)) (stack ygap infl) := by
  have hσσ : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  have hσσ' : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ
  have hSS : (σ + κ * φπ) * (σ + κ * φπ)⁻¹ = 1 := mul_inv_cancel₀ hS
  have hSS' : (σ + κ * φπ)⁻¹ * (σ + κ * φπ) = 1 := inv_mul_cancel₀ hS
  constructor
  · rintro ⟨hp, hd, -⟩ t j
    funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hp t) ω
    have r := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 r
    rw [r] at e1
    have hs : (σ + κ * φπ) * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω +
        (1 - β * φπ) * 𝔼.E t (infl (t + 1)) ω + (rn t ω - ρ) := by
      linear_combination σ * e1 - φπ * e2 -
        (ρ + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) * hσσ
    have hs2 : (σ + κ * φπ) * infl t ω = σ * κ * 𝔼.E t (ygap (t + 1)) ω +
        (κ + β * σ) * 𝔼.E t (infl (t + 1)) ω + κ * (rn t ω - ρ) := by
      linear_combination (σ + κ * φπ) * e2 + κ * hs
    fin_cases j
    · simp only [stack, forcing, A, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (σ + κ * φπ)⁻¹ * hs - ygap t ω * hSS'
    · simp only [stack, forcing, A, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (σ + κ * φπ)⁻¹ * hs2 - infl t ω * hSS'
  · intro h
    have hdis : ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t) ∧
        infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t := by
      intro t
      have h0 := h t 0
      have h1 := h t 1
      simp only [stack, forcing, A, Fin.isValue, Matrix.cons_val_zero, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
      have key : ∀ ω, (σ + κ * φπ) * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω +
            (1 - β * φπ) * 𝔼.E t (infl (t + 1)) ω + (rn t ω - ρ) ∧
          (σ + κ * φπ) * infl t ω = σ * κ * 𝔼.E t (ygap (t + 1)) ω +
            (κ + β * σ) * 𝔼.E t (infl (t + 1)) ω + κ * (rn t ω - ρ) := by
        intro ω
        have e0 := congrFun h0 ω
        have e1 := congrFun h1 ω
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
        constructor
        · linear_combination (σ + κ * φπ) * e0 + (σ * 𝔼.E t (ygap (t + 1)) ω +
            (1 - β * φπ) * 𝔼.E t (infl (t + 1)) ω + (rn t ω - ρ)) * hSS
        · linear_combination (σ + κ * φπ) * e1 + (σ * κ * 𝔼.E t (ygap (t + 1)) ω +
            (κ + β * σ) * 𝔼.E t (infl (t + 1)) ω + κ * (rn t ω - ρ)) * hSS
      have hn : ∀ ω, infl t ω = β * 𝔼.E t (infl (t + 1)) ω + κ * ygap t ω := by
        intro ω
        apply mul_left_cancel₀ hS
        linear_combination (key ω).2 - κ * (key ω).1
      refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
      · have r := congrFun (hrule t) ω
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
        rw [r]
        have hsig : σ * ygap t ω = σ * 𝔼.E t (ygap (t + 1)) ω -
            (ρ + φπ * infl t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) := by
          linear_combination (key ω).1 + φπ * hn ω
        linear_combination σ⁻¹ * hsig - (ygap t ω - 𝔼.E t (ygap (t + 1)) ω) * hσσ'
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact hn ω
    exact ⟨fun t => (hdis t).2, fun t => (hdis t).1, hrule⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: `tr A = (σ(1 + β) + κ)/(σ + κφ_π)`. -/
theorem tr2_A {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    tr2 (A β σ κ φπ) = (σ * (1 + β) + κ) / (σ + κ * φπ) := by
  simp only [tr2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(d), p. 91: `det A = σβ/(σ + κφ_π)`. -/
theorem det2_A {β σ κ φπ : ℝ} (hS : σ + κ * φπ ≠ 0) :
    det2 (A β σ κ φπ) = σ * β / (σ + κ * φπ) := by
  simp only [det2, A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp
  ring

/-- Galí (2015), Ex. 3.3(d), p. 91 (the Taylor principle): for `σ, κ > 0`, `0 < β < 1`,
`φ_π ≥ 0`, both eigenvalues of `A` lie inside the unit circle iff `φ_π > 1`. -/
theorem schurStable_iff {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) :
    SchurStable (tr2 (A β σ κ φπ)) (det2 (A β σ κ φπ)) ↔ 1 < φπ := by
  have hS : 0 < σ + κ * φπ := by positivity
  rw [tr2_A hS.ne', det2_A hS.ne']
  have hD0 : 0 < σ * β / (σ + κ * φπ) := by positivity
  have hD1 : σ * β / (σ + κ * φπ) < 1 := by
    rw [div_lt_one hS]; nlinarith
  have hT0 : 0 < (σ * (1 + β) + κ) / (σ + κ * φπ) := by positivity
  unfold SchurStable
  rw [abs_of_pos hD0, abs_of_pos hT0, one_add_div hS.ne', div_lt_div_iff_of_pos_right hS]
  constructor
  · rintro ⟨-, h⟩; nlinarith
  · intro h; exact ⟨hD1, by nlinarith⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: determinacy (at most one bounded adapted solution for
every forcing) holds iff `φ_π > 1`. -/
theorem determinate_iff [Nonempty Ω] {β σ κ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) : 𝔼.Determinate (A β σ κ φπ) ↔ 1 < φπ :=
  (𝔼.determinate_iff _).trans (schurStable_iff hσ hκ hβ0 hβ1 hφπ)

/-- Two bounded processes stack to a bounded vector process. -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process. -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), Ex. 3.3(c)–(d), p. 90: the composite coefficient
`c_g = σφ(1 − ρ_g)/(σ + φ)` of the natural-rate deviation `r^n_t − ρ = c_g g_t`. -/
noncomputable def cg (σ φ ρg : ℝ) : ℝ := σ * φ * (1 - ρg) / (σ + φ)

/-- Galí (2015), Ex. 3.3(d), p. 91: `Λ_g = 1/((1 − βρ_g) σ (1 − ρ_g) + κ (φ_π − ρ_g))`. -/
noncomputable def lam (β σ κ φπ ρg : ℝ) : ℝ := 1 / ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg))

/-- Galí (2015), Ex. 3.3(d), p. 91: `Λ_g > 0` for `φ_π > 1`, `ρ_g < 1`. -/
theorem lam_pos {β σ κ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφπ : 1 < φπ) (hρ1 : ρg < 1) : 0 < lam β σ κ φπ ρg := by
  have h1 : 0 < 1 - β * ρg := by nlinarith
  have h2 : 0 < (1 - β * ρg) * σ * (1 - ρg) := by
    have : 0 < 1 - ρg := by linarith
    positivity
  have h3 : 0 < κ * (φπ - ρg) := mul_pos hκ (by linarith)
  exact one_div_pos.mpr (by linarith)

/-- Galí (2015), Ex. 3.3(d), p. 91: the MSV output-gap coefficient `(1 − βρ_g) Λ_g c_g`. -/
noncomputable def psiY (β σ κ φ φπ ρg : ℝ) : ℝ := (1 - β * ρg) * lam β σ κ φπ ρg * cg σ φ ρg

/-- Galí (2015), Ex. 3.3(d), p. 91: the MSV inflation coefficient `κ Λ_g c_g`. -/
noncomputable def psiPi (β σ κ φ φπ ρg : ℝ) : ℝ := κ * lam β σ κ φπ ρg * cg σ φ ρg

/-- A scalar multiple of an AR(1) process is AR(1) with the same persistence. -/
theorem isAR1_smul {ρg : ℝ} {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (c : ℝ) :
    𝔼.IsAR1 ρg (fun t => c • g t) :=
  ⟨fun t => by simp only [map_smul, hg.1 t], fun t => by
    simp only [map_smul, hg.2 t, smul_comm c ρg]⟩

/-- A scalar multiple of a bounded process is bounded. -/
theorem bounded_smul {g : ℕ → Ω → ℝ} (hg : BoundedProc g) (c : ℝ) :
    BoundedProc (fun t => c • g t) := by
  obtain ⟨M, hM⟩ := hg
  exact ⟨|c| * M, fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: **existence** — with AR(1) purchases, the MSV processes
`ỹ_t = (1 − βρ_g) Λ_g c_g g_t`, `π_t = κ Λ_g c_g g_t`, `i_t = ρ + φ_π π_t` form an
equilibrium (the denominator of `Λ_g` being nonzero). -/
theorem msv_equilibrium {β σ κ φ ρ φπ ρg : ℝ} (hσ : σ ≠ 0) (hσφ : σ + φ ≠ 0)
    (hden : (1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg) ≠ 0) {g : ℕ → Ω → ℝ}
    (hg : 𝔼.IsAR1 ρg g) :
    Equilibrium 𝔼 β σ κ ρ φπ (natRate 𝔼 σ φ ρ g) (fun t => psiY β σ κ φ φπ ρg • g t)
      (fun t => psiPi β σ κ φ φπ ρg • g t)
      (fun t => (fun _ => ρ) + φπ • (psiPi β σ κ φ φπ ρg • g t)) := by
  have c1 : psiPi β σ κ φ φπ ρg = β * (psiPi β σ κ φ φπ ρg * ρg) + κ * psiY β σ κ φ φπ ρg := by
    unfold psiPi psiY
    ring
  have c2 : psiY β σ κ φ φπ ρg = psiY β σ κ φ φπ ρg * ρg - σ⁻¹ *
      (φπ * psiPi β σ κ φ φπ ρg - psiPi β σ κ φ φπ ρg * ρg - σ * φ * (1 - ρg) / (σ + φ)) := by
    unfold psiY psiPi lam cg
    field_simp
    ring
  refine ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩
  · funext ω
    simp only [map_smul, hg.2 t, smul_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination g t ω * c1
  · funext ω
    rw [natRate_ar1 𝔼 hg t]
    simp only [map_smul, hg.2 t, smul_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    linear_combination g t ω * c2

/-- Galí (2015), Ex. 3.3(d), p. 91: **the unique bounded equilibrium**. For `σ, κ, φ > 0`,
`0 < β < 1`, `φ_π > 1` and bounded AR(1) purchases with `ρ_g < 1` (the book has
`ρ_g ∈ [0, 1)`), a triple `(ỹ, π, i)` with bounded adapted `ỹ`, `π` is an equilibrium iff
it is the MSV triple. -/
theorem equilibrium_iff_msv {β σ κ φ ρ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hρ1 : ρg < 1)
    {g : ℕ → Ω → ℝ} (hg : 𝔼.IsAR1 ρg g) (hgb : BoundedProc g) {ygap infl i : ℕ → Ω → ℝ}
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    Equilibrium 𝔼 β σ κ ρ φπ (natRate 𝔼 σ φ ρ g) ygap infl i ↔
      ygap = (fun t => psiY β σ κ φ φπ ρg • g t) ∧
      infl = (fun t => psiPi β σ κ φ φπ ρg • g t) ∧
      i = fun t => (fun _ => ρ) + φπ • (psiPi β σ κ φ φπ ρg • g t) := by
  have hS : σ + κ * φπ ≠ 0 := by nlinarith
  have hσφ : σ + φ ≠ 0 := by linarith
  have hden : (1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg) ≠ 0 := by
    have := lam_pos hσ hκ hβ0 hβ1 hφπ hρ1
    unfold lam at this
    exact (one_div_pos.mp this).ne'
  have hmsv := msv_equilibrium 𝔼 (ρ := ρ) hσ.ne' hσφ hden hg
  constructor
  · intro he
    have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
    have hy := (equilibrium_iff_solves 𝔼 hσ.ne' hS hmsv.2.2).mp hmsv
    have heq := 𝔼.system_unique ((schurStable_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφπ) hx hy
      (adaptedVec_stack 𝔼 ha hb)
      (adaptedVec_stack 𝔼 (isAR1_smul 𝔼 hg _).1 (isAR1_smul 𝔼 hg _).1)
      (boundedVec_stack hba hbb) (boundedVec_stack (bounded_smul hgb _) (bounded_smul hgb _))
    have h1 : ygap = fun t => psiY β σ κ φ φπ ρg • g t :=
      funext fun t => by simpa [stack] using congrFun (congrFun heq t) 0
    have h2 : infl = fun t => psiPi β σ κ φ φπ ρg • g t :=
      funext fun t => by simpa [stack] using congrFun (congrFun heq t) 1
    refine ⟨h1, h2, funext fun t => ?_⟩
    rw [he.2.2 t, h2]
  · rintro ⟨rfl, rfl, rfl⟩
    exact hmsv

/-- Galí (2015), Ex. 3.3(d), p. 91: for `φ_π ≤ 1` the equilibrium is indeterminate: next to
any bounded adapted equilibrium there is a second one with a different gap or inflation. -/
theorem equilibrium_not_unique [Nonempty Ω] {β σ κ ρ φπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ0 : 0 ≤ φπ) (hφπ : φπ ≤ 1) {rn ygap infl i : ℕ → Ω → ℝ}
    (he : Equilibrium 𝔼 β σ κ ρ φπ rn ygap infl i) (ha : 𝔼.Adapted ygap)
    (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap) (hbb : BoundedProc infl) :
    ∃ ygap' infl' i', Equilibrium 𝔼 β σ κ ρ φπ rn ygap' infl' i' ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  have hS : σ + κ * φπ ≠ 0 := by positivity
  have hns : ¬ SchurStable (tr2 (A β σ κ φπ)) (det2 (A β σ κ φπ)) := by
    rw [schurStable_iff hσ hκ hβ0 hβ1 hφπ0]; linarith
  have hx := (equilibrium_iff_solves 𝔼 hσ.ne' hS he.2.2).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique hns hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  set ygap' : ℕ → Ω → ℝ := fun t => y t 0
  set infl' : ℕ → Ω → ℝ := fun t => y t 1
  have hst : stack ygap' infl' = y := by
    funext t j
    fin_cases j <;> rfl
  have hrule' : Rule ρ φπ (fun t => (fun _ => ρ) + φπ • infl' t) infl' := fun t => rfl
  refine ⟨ygap', infl', _, (equilibrium_iff_solves 𝔼 hσ.ne' hS hrule').mpr (hst ▸ hy),
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩, ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

/-- Galí (2015), Ex. 3.3(d), p. 91: **the response to a fiscal expansion**. For
`σ, κ, φ > 0`, `0 < β < 1`, `φ_π > 1`, `ρ_g < 1`: the output gap, inflation and the
nominal rate all rise with `g` (`ψ_y, ψ_π, φ_π ψ_π > 0`), as does the real rate
`i_t − E_t π_{t+1}`, whose coefficient is `(φ_π − ρ_g) ψ_π > 0`. -/
theorem msv_responses_pos {β σ κ φ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hρ1 : ρg < 1) :
    0 < psiY β σ κ φ φπ ρg ∧ 0 < psiPi β σ κ φ φπ ρg ∧ 0 < φπ * psiPi β σ κ φ φπ ρg ∧
      0 < (φπ - ρg) * psiPi β σ κ φ φπ ρg := by
  have hL := lam_pos hσ hκ hβ0 hβ1 hφπ hρ1
  have hc : 0 < cg σ φ ρg := by
    unfold cg
    have : 0 < 1 - ρg := by linarith
    positivity
  have h1 : 0 < 1 - β * ρg := by nlinarith
  have hP : 0 < psiPi β σ κ φ φπ ρg := by unfold psiPi; positivity
  refine ⟨by unfold psiY; positivity, hP, by positivity, mul_pos (by linarith) hP⟩

/-- Galí (2015), Ex. 3.3(d), p. 91: **the output multiplier under sticky prices**. Output is
`y_t = y^n_t + ỹ_t`, with multiplier `σ/(σ + φ) + ψ_y`; it strictly exceeds the flexible-price
multiplier `σ/(σ + φ)` and is strictly below one, so consumption is still crowded out
(`y − g` falls), but by less than under flexible prices. -/
theorem output_multiplier_bounds {β σ κ φ φπ ρg : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφ : 0 < φ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hρ1 : ρg < 1) :
    σ / (σ + φ) < σ / (σ + φ) + psiY β σ κ φ φπ ρg ∧
      σ / (σ + φ) + psiY β σ κ φ φπ ρg < 1 := by
  refine ⟨by linarith [(msv_responses_pos hσ hκ hφ hβ0 hβ1 hφπ hρ1).1], ?_⟩
  have h1 : 0 < 1 - β * ρg := by nlinarith
  have h2 : 0 < 1 - ρg := by linarith
  have hk : 0 < κ * (φπ - ρg) := mul_pos hκ (by linarith)
  have hd : 0 < (1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg) := by positivity
  have hσφ : 0 < σ + φ := by linarith
  unfold psiY lam cg
  rw [show σ / (σ + φ) + (1 - β * ρg) * (1 / ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg))) *
      (σ * φ * (1 - ρg) / (σ + φ)) = (σ * ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg)) +
        φ * ((1 - β * ρg) * σ * (1 - ρg))) / ((σ + φ) *
          ((1 - β * ρg) * σ * (1 - ρg) + κ * (φπ - ρg))) by field_simp]
  rw [div_lt_one (by positivity)]
  nlinarith

end Gali.BasicNewKeynesianModel.Ex3_3
