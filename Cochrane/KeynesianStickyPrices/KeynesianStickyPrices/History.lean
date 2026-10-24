/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TaylorDeterminacy

/-!
# History and implications

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 18, "History and
implications", pp. 422–432: the precise claims.

* Footnote 1, p. 424 (the Lucas critique): in the permanent-income model
  `c_t = r k_t + rβ E_t ∑ βʲ y_{t+j}` with `β = 1/(1 + r)` and AR(1) income,
  `c_t = r k_t + rβ/(1 − βη) y_t = r k_t + r/(1 + r − η) y_t` (`pih_consumption`, `mpc_eq`): the
  marginal propensity to consume depends on the persistence `η` (`mpc_strictMonoOn`,
  `mpc_injective`) — it is "a mongrel, … not a structural parameter".
* (18.1), p. 427: the Taylor rule with an output response (`Rule181`); in the three-equation
  model with `φ_π, φ_x ≥ 0` its equilibrium is determinate iff `κ(φ_π − 1) + (1 − β)φ_x > 0`
  (`rule181_determinate_iff`), so `φ_π > 1` "gives the eigenvalue you need"
  (`rule181_phi_gt_one`).
* (18.2), p. 427: the inertial, forward-looking rule (`Rule182`); with `φ_i = 0` and the rest
  zero it is (18.1) (`rule182_reduces`); without inertia its deviation system is a structural
  system `P x̃_t = Q E_t x̃_{t+1}` (`rule182_deviation_iff`), determinate iff `det P ≠ 0` and
  `P⁻¹Q` is Schur stable (`rule182_determinate_iff`).
* (18.3), p. 427, "write it King's way, and the likelihood function will be flat": any function
  of the equilibrium paths takes the same value for every `φ` in the determinacy region
  (`likelihood_flat`).
* p. 428, Clarida–Galí–Gertler: `φ_π > 1` means determinacy, but `φ_π < 1` means multiple
  equilibria only if the output response is small, `(1 − β)φ_x ≤ κ(1 − φ_π)` (`cgg_reading`).
-/

namespace Cochrane.KeynesianStickyPrices.History

open Filter Topology OptimalPolicy TaylorDeterminacy
open SharedTools (Pmat solvedA det2_Pmat)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The permanent-income footnote (p. 424) -/

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424: the marginal propensity to consume out of
current income, `r/(1 + r − η)`. -/
noncomputable def mpc (r η : ℝ) : ℝ := r / (1 + r - η)

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424: with `β = 1/(1 + r)`,
`rβ/(1 − βη) = r/(1 + r − η)`. -/
theorem mpc_eq {r η : ℝ} (hr : 0 < r) (hη : η < 1 + r) :
    r * (1 / (1 + r)) / (1 - 1 / (1 + r) * η) = mpc r η := by
  unfold mpc
  have h1 : (1 + r) ≠ 0 := by linarith
  have h2 : 1 + r - η ≠ 0 := by linarith
  field_simp

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424: in the rational-expectations permanent-income
model `c_t = r k_t + rβ E_t ∑_{j≥0} βʲ y_{t+j}` with `β = 1/(1 + r)`, `r > 0`, and AR(1) income
`E_t y_{t+1} = η y_t` with `|η| ≤ 1`, consumption is the Keynesian consumption function
`c_t = r k_t + r/(1 + r − η) · y_t`. -/
theorem pih_consumption {r η : ℝ} (hr : 0 < r) (hη : |η| ≤ 1) {y k : ℕ → Ω → ℝ}
    (hy : 𝔼.IsAR1 η y) (t : ℕ) (ω : Ω) :
    Summable (fun j => (1 / (1 + r)) ^ j * 𝔼.E t (y (t + j)) ω) ∧
      r * k t ω + r * (1 / (1 + r)) * ∑' j, (1 / (1 + r)) ^ j * 𝔼.E t (y (t + j)) ω =
        r * k t ω + mpc r η * y t ω := by
  have hβ0 : 0 < 1 / (1 + r) := by positivity
  have hβ1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hq : |1 / (1 + r) * η| < 1 := by
    rw [abs_mul, abs_of_pos hβ0]
    calc 1 / (1 + r) * |η| ≤ 1 / (1 + r) * 1 := by gcongr
      _ < 1 := by linarith
  have hterm : ∀ j, (1 / (1 + r)) ^ j * 𝔼.E t (y (t + j)) ω = y t ω * (1 / (1 + r) * η) ^ j := by
    intro j
    rw [𝔼.ar1_iterate hy t j, Pi.smul_apply, smul_eq_mul, mul_pow]
    ring
  simp_rw [hterm]
  refine ⟨(summable_geometric_of_abs_lt_one hq).mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hq, ← mpc_eq hr (by
    have := (abs_le.mp hη).2; linarith)]
  have : 1 - 1 / (1 + r) * η ≠ 0 := by
    have := (abs_lt.mp hq).2
    linarith
  field_simp

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424 ("if policy changes the persistence of income
… the marginal propensity to consume changes"): for `r > 0` the MPC is strictly increasing in
the persistence `η` on `η < 1 + r`. -/
theorem mpc_strictMonoOn {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (mpc r) (Set.Iio (1 + r)) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  unfold mpc
  apply div_lt_div_of_pos_left hr (by linarith) (by linarith)

/-- Cochrane (2023), Ch. 18 footnote 1, p. 424 ("the marginal propensity to consume is a
'mongrel'"): different persistences give different MPCs. -/
theorem mpc_injective {r η η' : ℝ} (hr : 0 < r) (hη : η < 1 + r) (hη' : η' < 1 + r)
    (hne : η ≠ η') : mpc r η ≠ mpc r η' :=
  ((mpc_strictMonoOn hr).injOn).ne (Set.mem_Iio.mpr hη) (Set.mem_Iio.mpr hη') hne

/-! ### The rules (18.1)–(18.3) -/

/-- Cochrane (2023), eq. (18.1), p. 427: `i_t = φ_π π_t + φ_x x_t + u_{i,t}`. -/
def Rule181 (φπ φx : ℝ) (u i x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = φπ • π t + φx • x t + u t

/-- Cochrane (2023), eq. (18.2), p. 427:
`i_t = φ_i i_{t−1} + φ_π π_t + φ_x x_t + φ_{π,1} E_t π_{t+1} + φ_{x,1} E_t x_{t+1} + u_{i,t}`
(from date 1 on). -/
def Rule182 (φi φπ φx φπ1 φx1 : ℝ) (u i x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i (t + 1) = φi • i t + φπ • π (t + 1) + φx • x (t + 1) +
    φπ1 • 𝔼.E (t + 1) (π (t + 2)) + φx1 • 𝔼.E (t + 1) (x (t + 2)) + u (t + 1)

/-- Cochrane (2023), eqs. (18.1)–(18.2): with no inertia and no forward responses, (18.2) is
(18.1) (from date 1 on). -/
theorem rule182_reduces (φπ φx : ℝ) (u i x π : ℕ → Ω → ℝ) :
    Rule182 𝔼 0 φπ φx 0 0 u i x π ↔ ∀ t, i (t + 1) = φπ • π (t + 1) + φx • x (t + 1) + u (t + 1) :=
  by simp [Rule182]

/-- Cochrane (2023), p. 427 ("you discover … that φ_π > 1 gives the eigenvalue you need for a
unique linearized solution"), restated: in the three-equation model with (18.1), `σ, κ > 0`,
`0 < β < 1`, `φ_π, φ_x ≥ 0`, the deviation system is determinate iff
`κ(φ_π − 1) + (1 − β)φ_x > 0`. -/
theorem rule181_determinate_iff [Nonempty Ω] {σ β κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    Determinate 𝔼 σ β κ φπ φx ↔ 0 < κ * (φπ - 1) + (1 - β) * φx :=
  determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφπ hφx

/-- Cochrane (2023), p. 427: with `φ_x ≥ 0`, `φ_π > 1` in (18.1) delivers determinacy. -/
theorem rule181_phi_gt_one [Nonempty Ω] {σ β κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hβ1 : β < 1) (hφπ : 1 < φπ) (hφx : 0 ≤ φx) : Determinate 𝔼 σ β κ φπ φx :=
  sufficient_of_phix_nonneg 𝔼 hσ hκ hβ hβ1 hφπ hφx

/-- Cochrane (2023), eq. (18.2), p. 427, without inertia: the structural matrix
`P = [[1 + σφ_x, σφ_π], [−κ, 1]]` and `Q = [[1 − σφ_{x,1}, σ(1 − φ_{π,1})], [0, β]]`. -/
def Q182 (σ β φπ1 φx1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - σ * φx1, σ * (1 - φπ1); 0, β]

/-- Cochrane (2023), eq. (18.2), p. 427: deviations under the forward-looking rule without
inertia, `ĩ = φ_π π̃ + φ_x x̃ + φ_{π,1} E π̃' + φ_{x,1} E x̃'`, with `x̃ = E x̃' − σ(ĩ − E π̃')`
and `π̃ = β E π̃' + κ x̃`, form the structural system `P x̃_t = Q E_t x̃_{t+1}`. -/
theorem rule182_deviation_iff (σ β κ φπ φx φπ1 φx1 : ℝ) (x π : ℕ → Ω → ℝ) :
    (∀ t, x t = 𝔼.E t (x (t + 1)) - σ • ((φπ • π t + φx • x t + φπ1 • 𝔼.E t (π (t + 1)) +
        φx1 • 𝔼.E t (x (t + 1))) - 𝔼.E t (π (t + 1))) ∧
      π t = β • 𝔼.E t (π (t + 1)) + κ • x t) ↔
      StructSolves 𝔼 (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1) (stack x π) := by
  constructor
  · intro h t j
    obtain ⟨h1, h2⟩ := h t
    funext ω
    have e1 := congrFun h1 ω
    have e2 := congrFun h2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    fin_cases j
    · simp only [Pmat, Q182, stack, Fin.zero_eta, Fin.isValue, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1
    · simp only [Pmat, Q182, stack, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      linear_combination e2
  · intro h t
    have e0 := h t 0
    have e1 := h t 1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have f := congrFun e0 ω
      simp only [Pmat, Q182, stack, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] at f
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination f
    · have f := congrFun e1 ω
      simp only [Pmat, Q182, stack, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul] at f
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination f

/-- Cochrane (2023), eq. (18.2), p. 427, without inertia: the deviation system is determinate iff
`det P = 1 + σφ_x + σκφ_π ≠ 0` and `P⁻¹Q` satisfies the Schur–Cohn condition. -/
theorem rule182_determinate_iff [Nonempty Ω] (σ β κ φπ φx φπ1 φx1 : ℝ) :
    StructDeterminate 𝔼 (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1) ↔
      1 + σ * φx + σ * κ * φπ ≠ 0 ∧
        SchurStable (tr2 (solvedA (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1)))
          (det2 (solvedA (Pmat σ κ φπ φx) (Q182 σ β φπ1 φx1))) := by
  rw [structDeterminate_iff, det2_Pmat]

/-- Cochrane (2023), eq. (18.3) and p. 427 ("write it King's way, and the likelihood function
will be flat"): for any statistic `L` of the equilibrium paths, and any `φ`, `φ'` in the
determinacy region, `L` takes the same value on the bounded adapted equilibria under King's
rule with `φ` and with `φ'`. -/
theorem likelihood_flat [Nonempty Ω] {σ β κ φ φ' : ℝ} (hdet : Determinate 𝔼 σ β κ φ 0)
    (hdet' : Determinate 𝔼 σ β κ φ' 0) {ux uπ istar xstar πstar : ℕ → Ω → ℝ}
    (hs : Starred 𝔼 σ β κ ux uπ istar xstar πstar) (hxs : 𝔼.Adapted xstar)
    (hπs : 𝔼.Adapted πstar) (hbxs : BoundedProc xstar) (hbπs : BoundedProc πstar)
    {β' : Type*} (L : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → β')
    {i x π i' x' π' : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hπ : 𝔼.Adapted π) (hbx : BoundedProc x)
    (hbπ : BoundedProc π) (hx' : 𝔼.Adapted x') (hπ' : 𝔼.Adapted π') (hbx' : BoundedProc x')
    (hbπ' : BoundedProc π') (he : KingEqm 𝔼 σ β κ φ ux uπ istar πstar i x π)
    (he' : KingEqm 𝔼 σ β κ φ' ux uπ istar πstar i' x' π') : L i x π = L i' x' π' := by
  obtain ⟨rfl, rfl, rfl⟩ := (phi_irrelevance 𝔼 hdet hs hxs hπs hbxs hbπs hx hπ hbx hbπ).mp he
  obtain ⟨rfl, rfl, rfl⟩ :=
    (phi_irrelevance 𝔼 hdet' hs hxs hπs hbxs hbπs hx' hπ' hbx' hbπ').mp he'
  rfl

/-- Cochrane (2023), p. 428 (Clarida, Galí and Gertler: "φ_π < 1 means multiple-equilibrium
volatility, and φ_π > 1 means determinacy"): with `φ_π ∈ [0, 1)` and `φ_x ≥ 0` the equilibrium
is indeterminate iff `(1 − β)φ_x ≤ κ(1 − φ_π)`, so the reading holds for small output
responses only. -/
theorem cgg_reading [Nonempty Ω] {σ β κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hβ1 : β < 1) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    ¬ Determinate 𝔼 σ β κ φπ φx ↔ (1 - β) * φx ≤ κ * (1 - φπ) := by
  rw [determinate_iff_BM 𝔼 hσ hκ hβ hβ1 hφπ hφx, not_lt]
  constructor <;> intro h <;> linarith

end Cochrane.KeynesianStickyPrices.History
