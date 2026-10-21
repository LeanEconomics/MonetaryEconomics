/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.CTRules
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.Matrix.Mul

/-!
# The continuous-time matrix method beyond real diagonalisable systems

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.13,
pp. 580–585 (the method used for the §5.7.3–§5.7.5 responses).

A1 §1.13 eigen-decomposes `A = QΛQ⁻¹` and sets the explosive modes to zero. `CTRules` proves this
for real diagonal `Λ`. This module covers complex eigenvalues and defective (non-diagonalisable)
`A`: the decomposition is a hypothesis `A = QJQ⁻¹` with `J` in Jordan form,
`J = diag(d) + N`, where `N` has the entries `e_k` on the superdiagonal. Mathlib has no
Jordan normal form theorem for matrices, so, like the book, we take the decomposition as given.
A real system is handled by complexification (`real_system_bounded_iff`), and complex-conjugate
pairs also appear as real `2 × 2` rotation blocks (`rotation_block_norm`,
`rotation_block_bounded_iff`).

## Main results

* Complex scalar modes: `cdecay_unique` (`w' = dw` gives `w = e^{dt}w₀`), `cresonant`
  (`w' = dw + ce^{dt}` gives `w = e^{dt}(w₀ + ct)`), `cstable_bounded` (`Re d < 0` with bounded
  forcing gives a bounded solution).
* `jordan_modes_bounded_iff`: for a Jordan chain system, every mode is bounded on `[0, ∞)` iff
  every mode with `Re d_k > 0` starts at zero **and** every non-leading mode of a block with
  `Re d_k = 0` starts at zero. So a zero-real-part eigenvalue with a nontrivial Jordan block
  (defective) admits only its eigenvector direction.
* `matrix_jordan_bounded_iff`: the same for `z' = Az`, `A = QJQ⁻¹`, through the modes `Q⁻¹z`;
  `matrix_cdiag_bounded_iff` is the diagonalisable-over-`ℂ` case (`e = 0`): bounded iff the modes
  with `Re d_k > 0` start at zero; `real_system_bounded_iff` is the same statement for a real
  system.
-/

namespace Cochrane.StickyPriceFiscal.CTMatrixMethod

open Filter Topology MeasureTheory Cochrane.StickyPriceFiscal.CTSimple

/-! ## Complex scalar modes -/

/-- Cochrane (2023), A1 §1.13, p. 583 (`e^{Λt}`): `t ↦ e^{ct}` (complex `c`, real time) has
derivative `c e^{ct}`. -/
theorem hasDerivAt_cexp_mul (c : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (c * u)) (c * Complex.exp (c * t)) t := by
  have h : HasDerivAt (fun x : ℂ => Complex.exp (c * x)) (Complex.exp (c * t) * c) (t : ℂ) := by
    have := ((hasDerivAt_id (t : ℂ)).const_mul c).cexp
    simpa using this
  exact h.comp_ofReal.congr_deriv (mul_comm _ _)

/-- Cochrane (2023), A1 §1.13, p. 583: `|e^{ct}| = e^{(Re c)t}`. -/
theorem norm_cexp_mul (c : ℂ) (t : ℝ) : ‖Complex.exp (c * t)‖ = Real.exp (c.re * t) := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- Cochrane (2023), A1 §1.13, p. 583: **a complex mode** `w' = dw` on `(0, ∞)`, `w` continuous on
`[0, ∞)`, is `w_t = e^{dt}w₀`. -/
theorem cdecay_unique {d : ℂ} {w : ℝ → ℂ} (hc : ContinuousOn w (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt w (d * w τ) τ) (t : ℝ) (ht : 0 ≤ t) :
    w t = Complex.exp (d * t) * w 0 := by
  have hG : ∀ τ ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun u : ℝ => Complex.exp (-d * u) * w u) ((fun _ => (0 : ℂ)) τ) τ :=
    fun τ hτ => ((hasDerivAt_cexp_mul (-d) τ).mul (hd τ hτ.1)).congr_deriv (by ring)
  have hGc : ContinuousOn (fun u : ℝ => Complex.exp (-d * u) * w u) (Set.Icc 0 t) :=
    ((by fun_prop : Continuous fun u : ℝ => Complex.exp (-d * u)).continuousOn.mul hc).mono
      Set.Icc_subset_Ici_self
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hGc hG
    (intervalIntegrable_const (μ := (volume : Measure ℝ)))
  simp only [intervalIntegral.integral_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    one_mul] at h
  have hinv : Complex.exp (d * t) * Complex.exp (-d * t) = 1 := by
    rw [← Complex.exp_add, show d * (t : ℂ) + -d * t = 0 by ring, Complex.exp_zero]
  linear_combination (-Complex.exp (d * t)) * h + (-(w t)) * hinv

/-- Cochrane (2023), A1 §1.13 (Jordan blocks): **resonant forcing**: `w' = dw + ce^{dt}` on
`(0, ∞)` gives `w_t = e^{dt}(w₀ + ct)`. -/
theorem cresonant {d c : ℂ} {w : ℝ → ℂ} (hc : ContinuousOn w (Set.Ici 0))
    (hd : ∀ τ, 0 < τ → HasDerivAt w (d * w τ + c * Complex.exp (d * τ)) τ) (t : ℝ)
    (ht : 0 ≤ t) : w t = Complex.exp (d * t) * (w 0 + c * t) := by
  have hcand : ∀ u : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (d * x) * (w 0 + c * x))
      (d * (Complex.exp (d * u) * (w 0 + c * u)) + c * Complex.exp (d * u)) u := fun u =>
    ((hasDerivAt_cexp_mul d u).mul
      (((hasDerivAt_id u).ofReal_comp.const_mul c).const_add (w 0))).congr_deriv (by
        simp only [Complex.ofReal_one, mul_one, id]; ring)
  have hcc : Continuous fun x : ℝ => Complex.exp (d * x) * (w 0 + c * x) := by fun_prop
  have h := cdecay_unique (d := d) (w := fun x => w x - Complex.exp (d * x) * (w 0 + c * x))
    (hc.sub hcc.continuousOn) (fun τ hτ => ((hd τ hτ).sub (hcand τ)).congr_deriv (by ring)) t ht
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul, sub_self]
    at h
  exact sub_eq_zero.1 h

/-- Cochrane (2023), A1 §1.13, p. 583: **a stable complex mode with bounded forcing**: if
`Re d < 0`, `w' = dw + f` on `(0, ∞)` with `f` continuous and `|f| ≤ M` on `[0, ∞)`, then
`|w_t| ≤ |w₀| + M/(−Re d)`. -/
theorem cstable_bounded {d : ℂ} {M : ℝ} {w f : ℝ → ℂ} (hre : d.re < 0)
    (hfc : ContinuousOn f (Set.Ici 0)) (hM : ∀ t, 0 ≤ t → ‖f t‖ ≤ M)
    (hc : ContinuousOn w (Set.Ici 0)) (hd : ∀ τ, 0 < τ → HasDerivAt w (d * w τ + f τ) τ)
    (t : ℝ) (ht : 0 ≤ t) : ‖w t‖ ≤ ‖w 0‖ + M / (-d.re) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 le_rfl)
  have hG : ∀ τ ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun u : ℝ => Complex.exp (-d * u) * w u)
      (Complex.exp (-d * τ) * f τ) τ :=
    fun τ hτ => ((hasDerivAt_cexp_mul (-d) τ).mul (hd τ hτ.1)).congr_deriv (by ring)
  have hGc : ContinuousOn (fun u : ℝ => Complex.exp (-d * u) * w u) (Set.Icc 0 t) :=
    ((by fun_prop : Continuous fun u : ℝ => Complex.exp (-d * u)).continuousOn.mul hc).mono
      Set.Icc_subset_Ici_self
  have hint : IntervalIntegrable (fun u : ℝ => Complex.exp (-d * u) * f u) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht
      (((by fun_prop : Continuous fun u : ℝ => Complex.exp (-d * u)).continuousOn.mul hfc).mono
        Set.Icc_subset_Ici_self)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hGc hG hint
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h
  have hinv : Complex.exp (d * t) * Complex.exp (-d * t) = 1 := by
    rw [← Complex.exp_add, show d * (t : ℂ) + -d * t = 0 by ring, Complex.exp_zero]
  have hw : w t = Complex.exp (d * t) * w 0 +
      Complex.exp (d * t) * ∫ u in (0 : ℝ)..t, Complex.exp (-d * u) * f u := by
    rw [h]
    linear_combination (-(w t)) * hinv
  -- bound the integral term
  have hb : ‖Complex.exp (d * t) * ∫ u in (0 : ℝ)..t, Complex.exp (-d * u) * f u‖ ≤
      M / (-d.re) := by
    rw [← intervalIntegral.integral_const_mul]
    have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
      (f := fun u => Complex.exp (d * t) * (Complex.exp (-d * u) * f u))
      (g := fun u => M * Real.exp (d.re * (t - u)))
      (ae_of_all _ fun u (hu : u ∈ Set.Ioc 0 t) => by
        have e : Complex.exp (d * t) * (Complex.exp (-d * u) * f u) =
            Complex.exp (d * ((t - u : ℝ) : ℂ)) * f u := by
          rw [← mul_assoc, ← Complex.exp_add]
          push_cast
          ring_nf
        rw [e, norm_mul, norm_cexp_mul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM u hu.1.le) (Real.exp_pos _).le)
      ((by fun_prop : Continuous fun u : ℝ => M * Real.exp (d.re * (t - u))).intervalIntegrable
        0 t)
    refine hle.trans ?_
    have hF : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun u => -M * Real.exp (d.re * (t - u)) / d.re)
        (M * Real.exp (d.re * (t - x))) x := by
      intro x _
      have h1 : HasDerivAt (fun u : ℝ => d.re * (t - u)) (-d.re) x :=
        ((hasDerivAt_id x).const_sub t |>.const_mul d.re).congr_deriv (by simp)
      have := ((h1.exp).const_mul (-M)).div_const d.re
      convert this using 1
      have ha : d.re ≠ 0 := by linarith
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
      ((by fun_prop : Continuous fun u : ℝ => M * Real.exp (d.re * (t - u))).intervalIntegrable
        0 t)]
    have ha : d.re ≠ 0 := by linarith
    have key : -M * Real.exp (d.re * (t - t)) / d.re - -M * Real.exp (d.re * (t - 0)) / d.re =
        M / (-d.re) * (1 - Real.exp (d.re * t)) := by
      rw [sub_self, sub_zero, mul_zero, Real.exp_zero]
      field_simp
      ring
    rw [key]
    have h0 : 0 ≤ M / (-d.re) := div_nonneg hM0 (by linarith)
    nlinarith [Real.exp_pos (d.re * t)]
  rw [hw]
  refine (norm_add_le _ _).trans (add_le_add ?_ hb)
  rw [norm_mul, norm_cexp_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.exp_le_one_iff]
  nlinarith

/-- Cochrane (2023), A1 §1.13 (infrastructure): a mode `e^{at}|w₀|` that stays bounded on
`[0, ∞)` with `a > 0` must start at zero. -/
theorem zero_of_exp_growth_bdd {a c K : ℝ} (ha : 0 < a) (hc : 0 ≤ c)
    (h : ∀ t, 0 ≤ t → Real.exp (a * t) * c ≤ K) : c = 0 := by
  by_contra hne
  have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hne)
  have hK : 0 ≤ K := le_trans (by positivity) (h 0 le_rfl)
  set t := K / (c * a)
  have h1 := h t (by positivity)
  have h2 := Real.add_one_le_exp (a * t)
  have h3 : c * (a * t) = K := by simp only [t]; field_simp
  nlinarith

/-! ## Jordan-chain systems -/

/-- Cochrane (2023), A1 §1.13: the coupling of mode `k` to mode `k + 1` in a Jordan chain,
`e_k w_{k+1}` (zero for the last mode). -/
noncomputable def jforce {n : ℕ} (e : Fin n → ℂ) (w : Fin n → ℝ → ℂ) (k : Fin n) (t : ℝ) : ℂ :=
  if h : k.val + 1 < n then e k * w ⟨k.val + 1, h⟩ t else 0

/-- Cochrane (2023), A1 §1.13: mode `k` is a non-leading member of a Jordan block
(`e_{k−1} ≠ 0`). -/
def NonLead {n : ℕ} (e : Fin n → ℂ) (k : Fin n) : Prop :=
  0 < k.val ∧ e ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩ ≠ 0

/-- Cochrane (2023), A1 §1.13: if mode `k` is coupled to mode `k + 1` (`e_k ≠ 0`), mode `k + 1`
is non-leading. -/
theorem nonLead_next {n : ℕ} {e : Fin n → ℂ} {k : Fin n} (h : k.val + 1 < n) (he : e k ≠ 0) :
    NonLead e ⟨k.val + 1, h⟩ := by
  refine ⟨Nat.succ_pos _, ?_⟩
  have : (⟨k.val + 1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) h⟩ : Fin n) = k := Fin.ext (by simp)
  simpa only [this] using he

/-- Cochrane (2023), A1 §1.13: the coupling term is continuous on `[0, ∞)`. -/
theorem jforce_continuousOn {n : ℕ} {e : Fin n → ℂ} {w : Fin n → ℝ → ℂ}
    (hc : ∀ k, ContinuousOn (w k) (Set.Ici 0)) (k : Fin n) :
    ContinuousOn (jforce e w k) (Set.Ici 0) := by
  unfold jforce
  split_ifs with h
  · exact continuousOn_const.mul (hc _)
  · exact continuousOn_const

/-- Cochrane (2023), A1 §1.13: if the next mode vanishes whenever it is coupled, the coupling
term vanishes and mode `k` is `w_k(t) = e^{d_k t}w_k(0)`. -/
theorem mode_free {n : ℕ} {d e : Fin n → ℂ} {w : Fin n → ℝ → ℂ} {k : Fin n}
    (hc : ∀ k, ContinuousOn (w k) (Set.Ici 0))
    (hd : ∀ k t, 0 < t → HasDerivAt (w k) (d k * w k t + jforce e w k t) t)
    (hz : ∀ h : k.val + 1 < n, e k ≠ 0 → ∀ t, 0 ≤ t → w ⟨k.val + 1, h⟩ t = 0) :
    ∀ t, 0 ≤ t → w k t = Complex.exp (d k * t) * w k 0 := by
  have hf : ∀ t, 0 < t → jforce e w k t = 0 := by
    intro t ht
    unfold jforce
    split_ifs with h
    · by_cases he : e k = 0
      · rw [he, zero_mul]
      · rw [hz h he t ht.le, mul_zero]
    · rfl
  exact cdecay_unique (hc k) fun τ hτ => (hd k τ hτ).congr_deriv (by rw [hf τ hτ, add_zero])

/-- Cochrane (2023), A1 §1.13, p. 583, generalised to Jordan chains: **bounded modes.** Let
`w_k' = d_k w_k + e_k w_{k+1}` on `(0, ∞)` (continuous on `[0, ∞)`), where `e_k ≠ 0` only inside
a Jordan block (`d_{k+1} = d_k`). Every mode is bounded on `[0, ∞)` iff every mode with
`Re d_k > 0` starts at zero and every non-leading mode of a block with `Re d_k = 0` starts at
zero. In particular a defective eigenvalue with zero real part admits only its eigenvector
direction, and the "stable = real part `≤ 0`" classification fails for it (E25). -/
theorem jordan_modes_bounded_iff {n : ℕ} {d e : Fin n → ℂ} {w : Fin n → ℝ → ℂ}
    (hJ : ∀ (k : Fin n) (h : k.val + 1 < n), e k ≠ 0 → d ⟨k.val + 1, h⟩ = d k)
    (hc : ∀ k, ContinuousOn (w k) (Set.Ici 0))
    (hd : ∀ k t, 0 < t → HasDerivAt (w k) (d k * w k t + jforce e w k t) t) :
    (∀ k, ∃ K, ∀ t, 0 ≤ t → ‖w k t‖ ≤ K) ↔
      ∀ k, (0 < (d k).re → w k 0 = 0) ∧ ((d k).re = 0 → NonLead e k → w k 0 = 0) := by
  constructor
  · intro hB
    -- downward induction on `n - 1 - k`
    have key : ∀ m (k : Fin n), n - 1 - k.val = m →
        (0 < (d k).re → ∀ t, 0 ≤ t → w k t = 0) ∧
          ((d k).re = 0 → NonLead e k → ∀ t, 0 ≤ t → w k t = 0) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro k hk
        have hnext : ∀ (h : k.val + 1 < n), e k ≠ 0 → 0 ≤ (d k).re →
            ∀ t, 0 ≤ t → w ⟨k.val + 1, h⟩ t = 0 := by
          intro h he hre
          have hdk := hJ k h he
          have := ih (n - 1 - (k.val + 1)) (by omega) ⟨k.val + 1, h⟩ rfl
          rcases lt_or_eq_of_le hre with hlt | heq
          · exact this.1 (by rw [hdk]; exact hlt)
          · exact this.2 (by rw [hdk]; exact heq.symm) (nonLead_next h he)
        refine ⟨fun hre => ?_, fun hre hnl => ?_⟩
        · have hfree := mode_free hc hd fun h he => hnext h he hre.le
          obtain ⟨K, hK⟩ := hB k
          have h0 : ‖w k 0‖ = 0 := zero_of_exp_growth_bdd hre (norm_nonneg _) fun t ht => by
            have := hK t ht
            rwa [hfree t ht, norm_mul, norm_cexp_mul] at this
          intro t ht
          rw [hfree t ht, norm_eq_zero.1 h0, mul_zero]
        · have hfree := mode_free hc hd fun h he => hnext h he hre.ge
          obtain ⟨hpos, hep⟩ := hnl
          set p : Fin n := ⟨k.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
          have hp1 : p.val + 1 < n := by simp only [p]; omega
          have hpk : (⟨p.val + 1, hp1⟩ : Fin n) = k := Fin.ext (by simp only [p]; omega)
          have hdp : d k = d p := by rw [← hJ p hp1 hep, hpk]
          have hres := cresonant (d := d p) (c := e p * w k 0) (w := w p) (hc p)
            (fun τ hτ => (hd p τ hτ).congr_deriv (by
              unfold jforce
              simp only [hp1, ↓reduceDIte]
              rw [hpk, hfree τ hτ.le, hdp]
              ring))
          obtain ⟨K, hK⟩ := hB p
          have hre' : (d p).re = 0 := by rw [← hdp]; exact hre
          have hbd : ∀ t : ℝ, 0 ≤ t → ‖w p 0 + e p * w k 0 * (t : ℂ)‖ ≤ K := fun t ht => by
            have := hK t ht
            rwa [hres t ht, norm_mul, norm_cexp_mul, hre', zero_mul, Real.exp_zero,
              one_mul] at this
          have hc0 : e p * w k 0 = 0 := by
            by_contra hne
            have hn : 0 < ‖e p * w k 0‖ := norm_pos_iff.2 hne
            set t := (K + ‖w p 0‖ + 1) / ‖e p * w k 0‖
            have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hbd 0 le_rfl)
            have ht : 0 ≤ t := by positivity
            have h1 := hbd t ht
            have h2 : ‖e p * w k 0 * (t : ℂ)‖ ≤ ‖w p 0 + e p * w k 0 * (t : ℂ)‖ + ‖w p 0‖ := by
              have := norm_sub_le (w p 0 + e p * w k 0 * (t : ℂ)) (w p 0)
              rwa [add_sub_cancel_left] at this
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht] at h2
            have h3 : ‖e p * w k 0‖ * t = K + ‖w p 0‖ + 1 := by
              simp only [t]; field_simp
            linarith
          have hw0 : w k 0 = 0 := (mul_eq_zero.1 hc0).resolve_left hep
          intro t ht
          rw [hfree t ht, hw0, mul_zero]
    intro k
    have := key _ k rfl
    exact ⟨fun hre => this.1 hre 0 le_rfl, fun hre hnl => this.2 hre hnl 0 le_rfl⟩
  · intro hC
    have key : ∀ m (k : Fin n), n - 1 - k.val = m →
        (∃ K, ∀ t, 0 ≤ t → ‖w k t‖ ≤ K) ∧ (0 < (d k).re → ∀ t, 0 ≤ t → w k t = 0) ∧
          ((d k).re = 0 → NonLead e k → ∀ t, 0 ≤ t → w k t = 0) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro k hk
        have ihn : ∀ h : k.val + 1 < n, _ := fun h =>
          ih (n - 1 - (k.val + 1)) (by omega) ⟨k.val + 1, h⟩ rfl
        rcases lt_trichotomy (d k).re 0 with hre | hre | hre
        · -- stable: bounded forcing
          have hfb : ∃ M, ∀ t, 0 ≤ t → ‖jforce e w k t‖ ≤ M := by
            by_cases h : k.val + 1 < n
            · obtain ⟨K, hK⟩ := (ihn h).1
              refine ⟨‖e k‖ * K, fun t ht => ?_⟩
              unfold jforce
              simp only [h, ↓reduceDIte]
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hK t ht) (norm_nonneg _)
            · exact ⟨0, fun t _ => by unfold jforce; simp only [h, ↓reduceDIte, norm_zero, le_refl]⟩
          obtain ⟨M, hM⟩ := hfb
          refine ⟨⟨‖w k 0‖ + M / (-(d k).re), cstable_bounded hre (jforce_continuousOn hc k) hM
            (hc k) (hd k)⟩, fun h => absurd h (by linarith), fun h => absurd h hre.ne⟩
        · have hfree := mode_free hc hd fun h he t ht => by
            have hdk := hJ k h he
            exact (ihn h).2.2 (by rw [hdk]; exact hre) (nonLead_next h he) t ht
          refine ⟨⟨‖w k 0‖, fun t ht => ?_⟩, fun h => absurd h (by linarith), fun _ hnl t ht => ?_⟩
          · rw [hfree t ht, norm_mul, norm_cexp_mul, hre, zero_mul, Real.exp_zero, one_mul]
          · rw [hfree t ht, (hC k).2 hre hnl, mul_zero]
        · have hfree := mode_free hc hd fun h he t ht => by
            have hdk := hJ k h he
            exact (ihn h).2.1 (by rw [hdk]; exact hre) t ht
          have hz : ∀ t, 0 ≤ t → w k t = 0 := fun t ht => by
            rw [hfree t ht, (hC k).1 hre, mul_zero]
          exact ⟨⟨0, fun t ht => by rw [hz t ht, norm_zero]⟩, fun _ => hz,
            fun h => absurd h hre.ne'⟩
    exact fun k => (key _ k rfl).1

/-! ## Matrix systems in Jordan form -/

/-- Cochrane (2023), A1 §1.13: the Jordan-form matrix `J = diag(d) + N`, with `N_{k,k+1} = e_k`. -/
noncomputable def jordanMat {n : ℕ} (d e : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal d + Matrix.of fun i j => if j.val = i.val + 1 then e i else 0

/-- Cochrane (2023), A1 §1.13: `(Jv)_k = d_k v_k + e_k v_{k+1}` (no second term for the last
row). -/
theorem jordanMat_mulVec {n : ℕ} (d e : Fin n → ℂ) (v : Fin n → ℂ) (k : Fin n) :
    (jordanMat d e).mulVec v k =
      d k * v k + (if h : k.val + 1 < n then e k * v ⟨k.val + 1, h⟩ else 0) := by
  rw [jordanMat, Matrix.add_mulVec, Pi.add_apply, Matrix.mulVec_diagonal]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, zero_mul]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k.val + 1, h⟩]
    · simp
    · intro j _ hj
      have : ¬ (j.val = k.val + 1) := fun hjv => hj (Fin.ext hjv)
      simp only [this, ↓reduceIte]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · refine Finset.sum_eq_zero fun j _ => ?_
    have : ¬ (j.val = k.val + 1) := fun hjv => h (hjv ▸ j.isLt)
    simp only [this, ↓reduceIte]

/-- Cochrane (2023), A1 §1.13, (1.52): **the modes of a Jordan-form system.** If `A = QJQ⁻¹`
and `z' = Az`, the modes `z̃ = Q⁻¹z` obey `z̃_k' = d_k z̃_k + e_k z̃_{k+1}`. -/
theorem jmodes_hasDerivAt {n : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℂ} {d e : Fin n → ℂ}
    {z : ℝ → Fin n → ℂ} {t : ℝ} (hA : A = Q * jordanMat d e * Qi) (hQ : Qi * Q = 1)
    (hz : HasDerivAt z (A.mulVec (z t)) t) (k : Fin n) :
    HasDerivAt (fun u => Qi.mulVec (z u) k)
      (d k * Qi.mulVec (z t) k + jforce e (fun j u => Qi.mulVec (z u) j) k t) t := by
  have hj := fun j => (hasDerivAt_pi.1 hz j).const_mul (Qi k j)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hj j
  have hval : Qi.mulVec (A.mulVec (z t)) = (jordanMat d e).mulVec (Qi.mulVec (z t)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA, ← mul_assoc, ← mul_assoc, hQ, one_mul]
  have hk := congrFun hval k
  rw [jordanMat_mulVec] at hk
  rw [show d k * Qi.mulVec (z t) k + jforce e (fun j u => Qi.mulVec (z u) j) k t =
    Qi.mulVec (A.mulVec (z t)) k by rw [hk]; rfl]
  exact hs

/-- Cochrane (2023), A1 §1.13, pp. 581–583: **the bounded responses of a Jordan-form system.**
For `z' = Az` after the news (`z` continuous on `[0, ∞)`), with `A = QJQ⁻¹`,
`J = diag(d) + N` a Jordan form (`e_k ≠ 0` only when `d_{k+1} = d_k`), `z` is bounded on
`[0, ∞)` iff every mode `(Q⁻¹z_0)_k` with `Re d_k > 0` is zero and every non-leading mode of a
block with `Re d_k = 0` is zero. This covers complex and defective eigenvalues. -/
theorem matrix_jordan_bounded_iff {n : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℂ}
    {d e : Fin n → ℂ} {z : ℝ → Fin n → ℂ} (hA : A = Q * jordanMat d e * Qi) (hQ : Qi * Q = 1)
    (hQ' : Q * Qi = 1) (hJ : ∀ (k : Fin n) (h : k.val + 1 < n), e k ≠ 0 → d ⟨k.val + 1, h⟩ = d k)
    (hc : ContinuousOn z (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t) :
    (∃ K, ∀ t, 0 ≤ t → ∀ j, ‖z t j‖ ≤ K) ↔
      ∀ k, (0 < (d k).re → Qi.mulVec (z 0) k = 0) ∧
        ((d k).re = 0 → NonLead e k → Qi.mulVec (z 0) k = 0) := by
  have hcm : ∀ k, ContinuousOn (fun u => Qi.mulVec (z u) k) (Set.Ici 0) := by
    intro k
    simp only [Matrix.mulVec, dotProduct]
    exact continuousOn_finsetSum _ fun j _ =>
      continuousOn_const.mul ((continuous_apply j).comp_continuousOn hc)
  rw [← jordan_modes_bounded_iff hJ hcm fun k t ht => jmodes_hasDerivAt hA hQ (hd t ht) k]
  constructor
  · rintro ⟨K, hK⟩ k
    refine ⟨∑ j, ‖Qi k j‖ * K, fun t ht => ?_⟩
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hK t ht j) (norm_nonneg _)
  · intro hB
    choose K hK using hB
    refine ⟨∑ j, ∑ k, ‖Q j k‖ * K k, fun t ht j => ?_⟩
    have hz : z t = Q.mulVec (Qi.mulVec (z t)) := by
      rw [Matrix.mulVec_mulVec, hQ', Matrix.one_mulVec]
    rw [hz]
    have hrow : ‖Q.mulVec (Qi.mulVec (z t)) j‖ ≤ ∑ k, ‖Q j k‖ * K k := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hK k t ht) (norm_nonneg _)
    refine hrow.trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ k, ‖Q j k‖ * K k)
      (fun j _ => Finset.sum_nonneg fun k _ =>
        mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) (hK k 0 le_rfl)))
      (Finset.mem_univ j)

/-- Cochrane (2023), A1 §1.13, p. 583, **diagonalisable over `ℂ`** (complex-conjugate eigenvalues
allowed): if `A = Q diag(d) Q⁻¹`, `z' = Az` is bounded on `[0, ∞)` iff every mode with
`Re d_k > 0` starts at zero ("explosive = positive real part"). -/
theorem matrix_cdiag_bounded_iff {n : ℕ} {A Q Qi : Matrix (Fin n) (Fin n) ℂ} {d : Fin n → ℂ}
    {z : ℝ → Fin n → ℂ} (hA : A = Q * Matrix.diagonal d * Qi) (hQ : Qi * Q = 1)
    (hQ' : Q * Qi = 1) (hc : ContinuousOn z (Set.Ici 0))
    (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t) :
    (∃ K, ∀ t, 0 ≤ t → ∀ j, ‖z t j‖ ≤ K) ↔ ∀ k, 0 < (d k).re → Qi.mulVec (z 0) k = 0 := by
  have hJm : jordanMat d (fun _ => 0) = Matrix.diagonal d := by
    rw [jordanMat]
    ext i j
    simp
  rw [matrix_jordan_bounded_iff (e := fun _ => 0) (by rw [hJm]; exact hA) hQ hQ'
    (fun _ _ h => absurd rfl h) hc hd]
  refine forall_congr' fun k => ⟨fun h => h.1, fun h => ⟨h, fun _ hnl => absurd rfl hnl.2⟩⟩

/-- Cochrane (2023), A1 §1.13 (the book's models are real): **a real system, by
complexification.** If the real matrix `A`, viewed in `ℂ`, is `QJQ⁻¹` with `J` in Jordan form,
then a real solution of `z' = Az` is bounded on `[0, ∞)` iff the complex modes of `z_0` satisfy
the conditions of `matrix_jordan_bounded_iff`. -/
theorem real_system_bounded_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {Q Qi : Matrix (Fin n) (Fin n) ℂ} {d e : Fin n → ℂ} {z : ℝ → Fin n → ℝ}
    (hA : A.map Complex.ofRealHom = Q * jordanMat d e * Qi) (hQ : Qi * Q = 1)
    (hQ' : Q * Qi = 1) (hJ : ∀ (k : Fin n) (h : k.val + 1 < n), e k ≠ 0 → d ⟨k.val + 1, h⟩ = d k)
    (hc : ContinuousOn z (Set.Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt z (A.mulVec (z t)) t) :
    (∃ K, ∀ t, 0 ≤ t → ∀ j, |z t j| ≤ K) ↔
      ∀ k, (0 < (d k).re → Qi.mulVec (Complex.ofRealHom ∘ z 0) k = 0) ∧
        ((d k).re = 0 → NonLead e k → Qi.mulVec (Complex.ofRealHom ∘ z 0) k = 0) := by
  have hcc : ContinuousOn (fun t => Complex.ofRealHom ∘ z t) (Set.Ici 0) :=
    continuousOn_pi.2 fun j => Complex.continuous_ofReal.comp_continuousOn
      ((continuous_apply j).comp_continuousOn hc)
  have hdc : ∀ t, 0 < t → HasDerivAt (fun t => Complex.ofRealHom ∘ z t)
      ((A.map Complex.ofRealHom).mulVec (Complex.ofRealHom ∘ z t)) t := by
    intro t ht
    refine hasDerivAt_pi.2 fun j => ?_
    have h := (hasDerivAt_pi.1 (hd t ht) j).ofReal_comp
    rw [← RingHom.map_mulVec]
    exact h
  rw [← matrix_jordan_bounded_iff hA hQ hQ' hJ hcc hdc]
  constructor <;> rintro ⟨K, hK⟩ <;> refine ⟨K, fun t ht j => ?_⟩
  · have := hK t ht j
    simpa [Complex.norm_real] using this
  · have := hK t ht j
    simpa [Complex.norm_real] using this

/-! ## Real `2 × 2` rotation blocks -/

/-- Cochrane (2023), A1 §1.13 (a complex-conjugate pair `a ± ib` as a real block): along
`u' = au − bw`, `w' = bu + aw` on `(0, ∞)`, `u_t² + w_t² = e^{2at}(u_0² + w_0²)`. -/
theorem rotation_block_norm {a b : ℝ} {u w : ℝ → ℝ} (hu : ContinuousOn u (Set.Ici 0))
    (hw : ContinuousOn w (Set.Ici 0)) (hdu : ∀ t, 0 < t → HasDerivAt u (a * u t - b * w t) t)
    (hdw : ∀ t, 0 < t → HasDerivAt w (b * u t + a * w t) t) (t : ℝ) (ht : 0 ≤ t) :
    u t ^ 2 + w t ^ 2 = Real.exp (2 * a * t) * (u 0 ^ 2 + w 0 ^ 2) := by
  have h := decay_unique (b := -(2 * a)) (w := fun x => u x ^ 2 + w x ^ 2)
    ((hu.pow 2).add (hw.pow 2))
    (fun τ hτ => (((hdu τ hτ).pow 2).add ((hdw τ hτ).pow 2)).congr_deriv (by
      simp only [Nat.cast_ofNat]; ring)) t ht
  rw [h]
  ring_nf

/-- Cochrane (2023), A1 §1.13, p. 583: **a real rotation block is bounded iff its real part is
non-positive or it starts at zero**: `(u, w)` is bounded on `[0, ∞)` iff `a ≤ 0` or
`u_0 = w_0 = 0`. -/
theorem rotation_block_bounded_iff {a b : ℝ} {u w : ℝ → ℝ} (hu : ContinuousOn u (Set.Ici 0))
    (hw : ContinuousOn w (Set.Ici 0)) (hdu : ∀ t, 0 < t → HasDerivAt u (a * u t - b * w t) t)
    (hdw : ∀ t, 0 < t → HasDerivAt w (b * u t + a * w t) t) :
    (∃ K, ∀ t, 0 ≤ t → u t ^ 2 + w t ^ 2 ≤ K) ↔ a ≤ 0 ∨ (u 0 = 0 ∧ w 0 = 0) := by
  have hN := rotation_block_norm hu hw hdu hdw
  constructor
  · rintro ⟨K, hK⟩
    by_cases ha : a ≤ 0
    · exact Or.inl ha
    · push Not at ha
      have h0 := zero_of_exp_growth_bdd (a := 2 * a) (by linarith)
        (by positivity : (0 : ℝ) ≤ u 0 ^ 2 + w 0 ^ 2) fun t ht => by rw [← hN t ht]; exact hK t ht
      right
      constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (w 0)]
  · rintro (ha | ⟨h1, h2⟩)
    · refine ⟨u 0 ^ 2 + w 0 ^ 2, fun t ht => ?_⟩
      rw [hN t ht]
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [Real.exp_le_one_iff]
      nlinarith
    · exact ⟨0, fun t ht => by rw [hN t ht, h1, h2]; simp⟩

end Cochrane.StickyPriceFiscal.CTMatrixMethod
