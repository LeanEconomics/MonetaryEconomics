/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.ForwardSolution
import DebtDeficitsInflation.ExpectationsFiniteTree

/-!
# Innovations and moving-average representations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2, eq. (4.1), p. 87,
and §4.2.7, pp. 97–98.

Chapter 4 is written in terms of the innovation operator `Δ_{t+1} = E_{t+1} − E_t` (the book's
`ΔE_{t+1}`) and moving-average representations `s_t = ∑_{j ≥ 0} a_j ε_{t−j} = a(L) ε_t` with a
martingale-difference shock `ε`. This module builds that language on top of the core
`ExpectationSystem`, so every later result holds under perfect foresight and under genuine
uncertainty.

* Shocks are indexed by `ℤ`, so that the moving average (4.1) has a genuine infinite past;
  processes are indexed by `ℕ` and information by `ℕ` (date-`0` information contains the
  pre-sample shocks).
* `innov 𝔼 t` is the linear map `Δ_{t+1}`; `innov_of_known`, `innov_mean_zero`, `innov_known`.
* `IsMDS`: a martingale-difference shock (`E_t ε_k = ε_k` for `k ≤ t`, `E_t ε_{t+1} = 0`);
  `E_shock` (`E_t ε_k` is `ε_k` or `0`), `innov_shock` (`Δ_{t+1} ε_k` is `ε_{t+1}` or `0`).
  `IsMDSNat`, `extendShock`: an `ℕ`-indexed MDS extended by zero to the past;
  `IsMDSNat.E_future`, `IsMDSNat.E_past` (used by the VAR/invertibility modules).
* `E_tsum_abs`: `E_t` commutes with `∑ c_j x_j` for absolutely summable weights `c` and
  uniformly bounded `x_j` (the generalisation of the core `E_tsum` from geometric weights).
* `IsMA`, `IsMAVec` (scalar and vector shocks, absolutely summable coefficients), `gen` (the
  generating function `a(z) = ∑ a_j zʲ`), `genVec`, `dotShock` (`c'ε_k`).
* `innov_MAVec`, `innov_MA` (`Δ_{t+1} s_{t+1+j} = a_j'ε_{t+1}`), `innov_PV_vec`, `innov_PV`
  (`Δ_{t+1} ∑ ρʲ s_{t+1+j} = a(ρ)'ε_{t+1}`), and the termwise version
  `innov_PV_termwise_vec` valid for every `|ρ| ≤ 1` (in particular `ρ = 1`).
* `ar1_of_MA`, `MA_of_ar1`, `isAR1_of_MA`: the AR(1) (4.3) and its moving average.
* `coinShockZ`: a genuinely random martingale-difference shock (two coin flips), used for the
  counterexamples of the later modules.
-/

namespace Cochrane.DebtDeficitsInflation.Innovations

open Filter Topology
open Cochrane.DebtDeficitsInflation.ExpectationsFiniteTree

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The innovation operator -/

/-- Cochrane (2023), §4.2, eq. (4.2), p. 87: the innovation operator `Δ_{t+1} := E_{t+1} − E_t`
(written `ΔE_{t+1}` in the book), a linear map on random variables. -/
def innov (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) := 𝔼.E (t + 1) - 𝔼.E t

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1} x = E_{t+1} x − E_t x`. -/
theorem innov_apply (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t x = 𝔼.E (t + 1) x - 𝔼.E t x := rfl

/-- Cochrane (2023), p. 65 ("since `v_t` is known at time `t`, it disappears from this
innovation accounting"): a variable known at `t` has no innovation at `t + 1`. -/
theorem innov_of_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : innov 𝔼 t x = 0 := by
  rw [innov_apply, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx, hx, sub_self]

/-- Cochrane (2023), eq. (4.2), p. 87: innovations are unpredictable, `E_t Δ_{t+1} x = 0`. -/
theorem innov_mean_zero (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (innov 𝔼 t x) = 0 := by
  rw [innov_apply, map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), eq. (4.2), p. 87: the innovation `Δ_{t+1} x` is known at `t + 1`. -/
theorem innov_known (t : ℕ) (x : Ω → ℝ) : 𝔼.E (t + 1) (innov 𝔼 t x) = innov 𝔼 t x := by
  rw [innov_apply, map_sub, 𝔼.E_E_self, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), eq. (3.20), p. 65 ("taking time `t+1` innovations" of an expectation):
`Δ_{t+1} (E_m x) = Δ_{t+1} x` for every `m ≥ t + 1`. -/
theorem innov_E_of_le {t m : ℕ} (hm : t + 1 ≤ m) (x : Ω → ℝ) :
    innov 𝔼 t (𝔼.E m x) = innov 𝔼 t x := by
  rw [innov_apply, innov_apply, 𝔼.tower hm, 𝔼.tower (le_trans (Nat.le_succ t) hm)]

/-- Cochrane (2023), eq. (4.2), p. 87: for `x` known at `t + 1`, `Δ_{t+1} x = x − E_t x`. -/
theorem innov_of_known_succ {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    innov 𝔼 t x = x - 𝔼.E t x := by
  rw [innov_apply, hx]

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1}` of a constant is zero. -/
theorem innov_const (t : ℕ) (c : ℝ) : innov 𝔼 t (fun _ => c) = 0 :=
  innov_of_known 𝔼 (𝔼.const t c)

/-! ### Martingale-difference shocks -/

/-- Cochrane (2023), eq. (4.1), p. 87: a martingale-difference shock `ε_k`, `k ∈ ℤ`: known at
every date `t ≥ k`, and unpredictable one period ahead, `E_t ε_{t+1} = 0`. -/
def IsMDS (ε : ℤ → Ω → ℝ) : Prop :=
  (∀ (t : ℕ) (k : ℤ), k ≤ t → 𝔼.E t (ε k) = ε k) ∧ ∀ t : ℕ, 𝔼.E t (ε ((t : ℤ) + 1)) = 0

/-- Cochrane (2023), eq. (4.1), p. 87: a vector martingale-difference shock (each component is
a martingale difference). -/
def IsMDSVec {n : ℕ} (ε : ℤ → Fin n → Ω → ℝ) : Prop := ∀ i, IsMDS 𝔼 (fun k => ε k i)

/-- Cochrane (2023), eq. (4.1), p. 87: a martingale difference is unpredictable at every
horizon, `E_t ε_k = 0` for `k > t`. -/
theorem E_shock_eq_zero {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) {t : ℕ} {k : ℤ} (hk : (t : ℤ) < k) :
    𝔼.E t (ε k) = 0 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = ((t + n : ℕ) : ℤ) + 1 := ⟨(k - t - 1).toNat, by omega⟩
  rw [← 𝔼.tower (Nat.le_add_right t n), hn, h.2 (t + n), map_zero]

/-- Cochrane (2023), eq. (4.1), p. 87: `E_t ε_k = ε_k` if `k ≤ t` and `0` otherwise. -/
theorem E_shock {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) (t : ℕ) (k : ℤ) :
    𝔼.E t (ε k) = if k ≤ t then ε k else 0 := by
  split_ifs with hk
  · exact h.1 t k hk
  · exact E_shock_eq_zero 𝔼 h (by omega)

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1} ε_k = ε_{t+1}` if `k = t + 1` and `0`
otherwise. -/
theorem innov_shock {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) (t : ℕ) (k : ℤ) :
    innov 𝔼 t (ε k) = if k = (t : ℤ) + 1 then ε k else 0 := by
  rw [innov_apply, E_shock 𝔼 h, E_shock 𝔼 h]
  rcases lt_trichotomy k ((t : ℤ) + 1) with hk | hk | hk
  · have h1 : k ≤ ((t + 1 : ℕ) : ℤ) := by push_cast; omega
    have h2 : k ≤ (t : ℤ) := by omega
    have h3 : k ≠ (t : ℤ) + 1 := by omega
    simp only [h1, h2, h3, ↓reduceIte, sub_self]
  · subst hk
    have h1 : (t : ℤ) + 1 ≤ ((t + 1 : ℕ) : ℤ) := by push_cast; omega
    have h2 : ¬ ((t : ℤ) + 1 ≤ (t : ℤ)) := by omega
    simp only [h1, h2, ↓reduceIte, sub_zero]
  · have h1 : ¬ k ≤ ((t + 1 : ℕ) : ℤ) := by push_cast; omega
    have h2 : ¬ k ≤ (t : ℤ) := by omega
    have h3 : k ≠ (t : ℤ) + 1 := by omega
    simp only [h1, h2, h3, ↓reduceIte, sub_self]

/-- Cochrane (2023), §4.2.7, p. 98: componentwise version of `innov_shock` for a vector
martingale-difference shock. -/
theorem innov_shock_vec {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (h : IsMDSVec 𝔼 ε) (i : Fin n) (t : ℕ)
    (k : ℤ) : innov 𝔼 t (ε k i) = if k = (t : ℤ) + 1 then ε k i else 0 :=
  innov_shock 𝔼 (ε := fun k => ε k i) (h i) t k

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed martingale difference (adapted, with
`E_t e_{t+1} = 0`). -/
def IsMDSNat (e : ℕ → Ω → ℝ) : Prop := 𝔼.Adapted e ∧ ∀ t, 𝔼.E t (e (t + 1)) = 0

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed martingale difference has zero forecast at
every horizon, `E_t e_{t+1+k} = 0`. -/
theorem IsMDSNat.E_future {𝔼 : ExpectationSystem Ω} {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e)
    (t k : ℕ) : 𝔼.E t (e (t + 1 + k)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t k), show t + 1 + k = t + k + 1 by omega, h.2 (t + k),
    map_zero]

/-- Cochrane (2023), eq. (4.1), p. 87: a past `ℕ`-indexed shock is known,
`E_t e_s = e_s` for `s ≤ t`. -/
theorem IsMDSNat.E_past {𝔼 : ExpectationSystem Ω} {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e)
    {s t : ℕ} (hst : s ≤ t) : 𝔼.E t (e s) = e s := by
  rw [← h.1 s, 𝔼.known hst]

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed shock extended by zero to dates `k ≤ 0`
(no shocks before the sample). -/
def extendShock (e : ℕ → Ω → ℝ) (k : ℤ) : Ω → ℝ := if 0 < k then e k.toNat else 0

/-- Cochrane (2023), eq. (4.1), p. 87: the zero-extension of an `ℕ`-indexed martingale
difference is a martingale difference. -/
theorem isMDS_extendShock {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e) : IsMDS 𝔼 (extendShock e) := by
  refine ⟨fun t k hk => ?_, fun t => ?_⟩
  · unfold extendShock
    split_ifs with hk0
    · exact ForwardSolution.E_of_known 𝔼 (by omega) (h.1 k.toNat)
    · exact map_zero _
  · unfold extendShock
    have h0 : (0 : ℤ) < (t : ℤ) + 1 := by omega
    rw [show ((t : ℤ) + 1).toNat = t + 1 by omega]
    simp only [h0, ↓reduceIte]
    exact h.2 t

/-- Cochrane (2023), eq. (4.1), p. 87: the zero-extension is bounded by any bound of the
original shock. -/
theorem extendShock_bounded {e : ℕ → Ω → ℝ} {M : ℝ} (hM : 0 ≤ M) (he : ∀ t ω, |e t ω| ≤ M)
    (k : ℤ) (ω : Ω) : |extendShock e k ω| ≤ M := by
  unfold extendShock
  split_ifs
  · exact he _ ω
  · simpa using hM

/-! ### Expectations of absolutely summable series -/

/-- Cochrane (2023), eq. (4.2), p. 87 (survey "new infrastructure" item 1): `E_t` commutes
with `∑ c_j x_j` for absolutely summable weights `c` and uniformly bounded `x_j`, generalising
the geometric-weight `E_tsum` of the core. -/
theorem E_tsum_abs {c : ℕ → ℝ} (hc : Summable fun j => |c j|) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ j ω, |x j ω| ≤ M) (t : ℕ) (ω : Ω) :
    𝔼.E t (fun ω' => ∑' j, c j * x j ω') ω = ∑' j, c j * 𝔼.E t (x j) ω := by
  have h := ForwardSolution.E_tsum_dom 𝔼 (hc.mul_right M) (f := fun j => c j • x j)
    (fun j ω' => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hx j ω') (abs_nonneg _)) t ω
  simpa only [Pi.smul_apply, smul_eq_mul, map_smul] using h

/-- Cochrane (2023), eq. (4.2), p. 87: with absolutely summable weights the series of
conditional expectations is summable. -/
theorem summable_E_terms {c : ℕ → ℝ} (hc : Summable fun j => |c j|) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ j ω, |x j ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable fun j => c j * 𝔼.E t (x j) ω :=
  Summable.of_norm_bounded (hc.mul_right M) fun j => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hx j) t ω) (abs_nonneg _)

/-- Cochrane (2023), eq. (4.2), p. 87: `Δ_{t+1}` commutes with `∑ c_j x_j` for absolutely
summable weights and bounded `x_j`. -/
theorem innov_tsum_abs {c : ℕ → ℝ} (hc : Summable fun j => |c j|) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ j ω, |x j ω| ≤ M) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (fun ω' => ∑' j, c j * x j ω') ω = ∑' j, c j * innov 𝔼 t (x j) ω := by
  rw [innov_apply, Pi.sub_apply, E_tsum_abs 𝔼 hc hx, E_tsum_abs 𝔼 hc hx,
    ← (summable_E_terms 𝔼 hc hx _ ω).tsum_sub (summable_E_terms 𝔼 hc hx _ ω)]
  refine tsum_congr fun j => ?_
  rw [innov_apply, Pi.sub_apply, mul_sub]

/-! ### Moving-average representations -/

/-- Cochrane (2023), eq. (4.2), p. 87: the generating function `a(z) = ∑_{j ≥ 0} a_j zʲ` of a
coefficient sequence (the book's `a(ρ)`, `a(β)`). -/
noncomputable def gen (a : ℕ → ℝ) (z : ℝ) : ℝ := ∑' j, a j * z ^ j

/-- Cochrane (2023), eq. (4.1), p. 87: `s` has the moving-average representation
`s_t = ∑_{j ≥ 0} a_j ε_{t−j}` with absolutely summable coefficients. -/
def IsMA (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  Summable (fun j => |a j|) ∧ ∀ t ω, s t ω = ∑' j, a j * ε ((t : ℤ) - j) ω

/-- Cochrane (2023), §4.2.7, p. 97: a vector moving average `s_t = a(L)'ε_t =
∑_{j ≥ 0} ∑_i a_{j,i} ε_{t−j,i}` with absolutely summable coefficients. -/
def IsMAVec {n : ℕ} (a : ℕ → Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  (∀ i, Summable (fun j => |a j i|)) ∧ ∀ t ω, s t ω = ∑' j, ∑ i, a j i * ε ((t : ℤ) - j) i ω

/-- Cochrane (2023), §4.2.7, p. 98: the vector `a(z) = ∑_j a_j zʲ` of generating functions. -/
noncomputable def genVec {n : ℕ} (a : ℕ → Fin n → ℝ) (z : ℝ) (i : Fin n) : ℝ :=
  gen (fun j => a j i) z

/-- Cochrane (2023), §4.2.7, p. 98: the scalar product `c'ε_k` of a coefficient vector and a
shock. -/
def dotShock {n : ℕ} (c : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) : Ω → ℝ :=
  fun ω => ∑ i, c i * ε k i ω

/-- Cochrane (2023), §4.2.7, p. 98: `a(0) = a_0`. -/
theorem gen_zero (a : ℕ → ℝ) : gen a 0 = a 0 := by
  unfold gen
  rw [tsum_eq_single 0 fun j hj => by simp [zero_pow hj]]
  simp

/-- Cochrane (2023), eq. (4.2), p. 87: absolutely summable coefficients give a summable
`∑ a_j zʲ` for `|z| ≤ 1`. -/
theorem summable_coeff_mul_pow {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {z : ℝ}
    (hz : |z| ≤ 1) : Summable fun j => a j * z ^ j :=
  Summable.of_norm_bounded ha fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz)

/-- Cochrane (2023), eq. (4.1), p. 87: a scalar moving average is the one-shock case of the
vector moving average. -/
theorem isMA_iff_vec (a : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (s : ℕ → Ω → ℝ) :
    IsMA a ε s ↔ IsMAVec (n := 1) (fun j _ => a j) (fun k _ => ε k) s := by
  simp [IsMA, IsMAVec]

/-- Cochrane (2023), eq. (4.1), p. 87: a scalar martingale difference is a one-component
vector martingale difference. -/
theorem isMDSVec_of_isMDS {ε : ℤ → Ω → ℝ} (h : IsMDS 𝔼 ε) :
    IsMDSVec 𝔼 (n := 1) (fun k _ => ε k) := fun _ => h

/-- Cochrane (2023), eq. (4.1), p. 87: the date-`k` terms of a vector moving average are
dominated by `∑_i |a_{j,i}| M`. -/
theorem abs_ma_term_le {n : ℕ} (a : ℕ → Fin n → ℝ) {ε : ℤ → Fin n → Ω → ℝ} {M : ℝ}
    (hε : ∀ k i ω, |ε k i ω| ≤ M) (j : ℕ) (k : ℤ) (ω : Ω) :
    |∑ i, a j i * ε k i ω| ≤ ∑ i, |a j i| * M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hε k i ω) (abs_nonneg _)

/-- Cochrane (2023), eq. (4.1), p. 87: the dominating sequence `∑_i |a_{j,i}| M` is summable. -/
theorem summable_ma_bound {n : ℕ} {a : ℕ → Fin n → ℝ} (ha : ∀ i, Summable fun j => |a j i|)
    (M : ℝ) : Summable fun j => ∑ i, |a j i| * M :=
  summable_sum fun i _ => (ha i).mul_right M

/-- Cochrane (2023), eq. (4.1), p. 87: conditional expectations of a vector moving average,
`E_m s_t = ∑_j ∑_i a_{j,i} E_m ε_{t−j,i}` (`E_m` commutes with the infinite sum). -/
theorem E_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) {M : ℝ} (hε : ∀ k i ω, |ε k i ω| ≤ M) (m t : ℕ) (ω : Ω) :
    𝔼.E m (s t) ω = ∑' j, ∑ i, a j i * 𝔼.E m (ε ((t : ℤ) - j) i) ω := by
  have hst : s t = fun ω' => ∑' j, (∑ i, a j i • ε ((t : ℤ) - j) i) ω' := by
    funext ω'
    rw [hs.2 t ω']
    simp [Finset.sum_apply]
  rw [hst, ForwardSolution.E_tsum_dom 𝔼 (summable_ma_bound hs.1 M)
    (fun j ω' => by simpa [Finset.sum_apply] using abs_ma_term_le a hε j _ ω') m ω]
  simp [map_sum, Finset.sum_apply]

/-- Cochrane (2023), eq. (4.1), p. 87: the series of conditional expectations of the terms of a
vector moving average is summable. -/
theorem summable_E_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    (ha : ∀ i, Summable fun j => |a j i|) {M : ℝ} (hε : ∀ k i ω, |ε k i ω| ≤ M)
    (m t : ℕ) (ω : Ω) :
    Summable fun j => ∑ i, a j i * 𝔼.E m (ε ((t : ℤ) - j) i) ω :=
  Summable.of_norm_bounded (summable_ma_bound ha M) fun j => by
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hε _ i) m ω) (abs_nonneg _)

/-- Cochrane (2023), eq. (4.1), p. 87: a moving average in a bounded shock is bounded, by
`∑_i (∑_j |a_{j,i}|) M`. -/
theorem abs_MAVec_le {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) {M : ℝ} (hε : ∀ k i ω, |ε k i ω| ≤ M) (t : ℕ) (ω : Ω) :
    |s t ω| ≤ ∑ i, (∑' j, |a j i|) * M := by
  have hsum : Summable fun j => ∑ i, a j i * ε ((t : ℤ) - j) i ω :=
    Summable.of_norm_bounded (summable_ma_bound hs.1 M) fun j => by
      rw [Real.norm_eq_abs]; exact abs_ma_term_le a hε j _ ω
  have hbound : ∑' j, ∑ i, |a j i| * M = ∑ i, (∑' j, |a j i|) * M := by
    rw [Summable.tsum_finsetSum fun i _ => (hs.1 i).mul_right M]
    exact Finset.sum_congr rfl fun i _ => tsum_mul_right
  rw [hs.2 t ω, ← hbound]
  calc |∑' j, ∑ i, a j i * ε ((t : ℤ) - j) i ω|
      = ‖∑' j, ∑ i, a j i * ε ((t : ℤ) - j) i ω‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖∑ i, a j i * ε ((t : ℤ) - j) i ω‖ := norm_tsum_le_tsum_norm
      (hsum.abs.congr fun j => (Real.norm_eq_abs _).symm)
    _ = ∑' j, |∑ i, a j i * ε ((t : ℤ) - j) i ω| := by simp_rw [Real.norm_eq_abs]
    _ ≤ ∑' j, ∑ i, |a j i| * M :=
        Summable.tsum_le_tsum (fun j => abs_ma_term_le a hε j _ ω) hsum.abs
          (summable_ma_bound hs.1 M)

/-- Cochrane (2023), eq. (4.1), p. 87: a moving average in a martingale-difference shock is
adapted, `E_t s_t = s_t`. -/
theorem adapted_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M) :
    𝔼.Adapted s := by
  intro t
  funext ω
  rw [E_MAVec 𝔼 hs hM t t ω, hs.2 t ω]
  refine tsum_congr fun j => Finset.sum_congr rfl fun i _ => ?_
  rw [(hε i).1 t _ (by omega)]

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent): the innovation in a future
value of a vector moving average is the corresponding coefficient,
`Δ_{t+1} s_{t+1+j} = a_j'ε_{t+1}`. -/
theorem innov_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    (t j : ℕ) : innov 𝔼 t (s (t + 1 + j)) = dotShock (a j) ε ((t : ℤ) + 1) := by
  funext ω
  rw [innov_apply, Pi.sub_apply, E_MAVec 𝔼 hs hM, E_MAVec 𝔼 hs hM,
    ← (summable_E_MAVec 𝔼 hs.1 hM _ _ ω).tsum_sub (summable_E_MAVec 𝔼 hs.1 hM _ _ ω)]
  have hterm : ∀ k, ∑ i, a k i * 𝔼.E (t + 1) (ε (((t + 1 + j : ℕ) : ℤ) - k) i) ω -
      ∑ i, a k i * 𝔼.E t (ε (((t + 1 + j : ℕ) : ℤ) - k) i) ω =
      if k = j then dotShock (a j) ε ((t : ℤ) + 1) ω else 0 := by
    intro k
    rw [← Finset.sum_sub_distrib]
    by_cases hk : k = j
    · subst hk
      have hm : ((t + 1 + k : ℕ) : ℤ) - (k : ℤ) = (t : ℤ) + 1 := by push_cast; ring
      simp only [hm, ↓reduceIte, dotShock]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_sub]
      congr 1
      have := congrFun (innov_shock_vec 𝔼 hε i t ((t : ℤ) + 1)) ω
      simpa only [innov_apply, ↓reduceIte, Pi.sub_apply] using this
    · have hm : ((t + 1 + j : ℕ) : ℤ) - (k : ℤ) ≠ (t : ℤ) + 1 := by push_cast; omega
      simp only [hk, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← mul_sub]
      have := congrFun (innov_shock_vec 𝔼 hε i t (((t + 1 + j : ℕ) : ℤ) - k)) ω
      simp only [hm, ↓reduceIte, innov_apply, Pi.sub_apply, Pi.zero_apply] at this
      rw [this, mul_zero]
  simp_rw [hterm]
  exact tsum_ite_eq j _

/-- Cochrane (2023), eq. (4.2), p. 87: scalar version of `innov_MAVec`,
`Δ_{t+1} s_{t+1+j} = a_j ε_{t+1}`. -/
theorem innov_MA {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) = a j • ε ((t : ℤ) + 1) := by
  rw [innov_MAVec 𝔼 ((isMA_iff_vec a ε s).1 hs) (isMDSVec_of_isMDS 𝔼 hε)
    (fun k _ ω => hM k ω) t j]
  funext ω
  simp [dotShock]

/-- Cochrane (2023), eq. (4.4), p. 88: with the normalisation `a_0 = 1`, the shock is the
surplus innovation, `Δ_{t+1} s_{t+1} = ε_{t+1}`. -/
theorem innov_MA_zero {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) :
    innov 𝔼 t (s (t + 1)) = ε ((t : ℤ) + 1) := by
  simpa [ha0] using innov_MA 𝔼 hs hε hM t 0

/-- Cochrane (2023), eq. (4.2), p. 87: the generating-function sum `∑_i a_i(ρ) c_i` written
as an infinite sum of the coefficients. -/
theorem hasSum_dot_gen {n : ℕ} {a : ℕ → Fin n → ℝ} {z : ℝ}
    (ha : ∀ i, Summable fun j => a j i * z ^ j) (e : Fin n → ℝ) :
    HasSum (fun j => z ^ j * ∑ i, a j i * e i) (∑ i, genVec a z i * e i) := by
  have h := hasSum_sum (s := Finset.univ) fun i _ => ((ha i).hasSum.mul_right (e i))
  convert h using 1
  · funext j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rfl

/-- Cochrane (2023), eq. (4.2), p. 87, termwise form valid for every `ρ` with
`∑ |a_j ρʲ| < ∞` (in particular `|ρ| ≤ 1`, including `ρ = 1`):
`∑_j ρʲ Δ_{t+1} s_{t+1+j} = a(ρ)'ε_{t+1}`. -/
theorem innov_PV_termwise_vec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : ∀ i, Summable fun j => a j i * ρ ^ j)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      (dotShock (genVec a ρ) ε ((t : ℤ) + 1) ω) := by
  simp_rw [innov_MAVec 𝔼 hs hε hM]
  exact hasSum_dot_gen hρ _

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992): for `|ρ| < 1`, the
innovation in the discounted sum of a vector moving average is `a(ρ)'ε_{t+1}`:
`Δ_{t+1} ∑_j ρʲ s_{t+1+j} = a(ρ)'ε_{t+1}`. -/
theorem innov_PV_vec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    innov 𝔼 t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω) = dotShock (genVec a ρ) ε ((t : ℤ) + 1) := by
  funext ω
  have hgeo : Summable fun j => |ρ ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  rw [innov_tsum_abs 𝔼 hgeo (fun j ω' => abs_MAVec_le hs hM (t + 1 + j) ω') t ω]
  exact (innov_PV_termwise_vec 𝔼 hs hε hM
    (fun i => summable_coeff_mul_pow (hs.1 i) hρ.le) t ω).tsum_eq

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992): for `|ρ| < 1`,
`Δ_{t+1} ∑_j ρʲ s_{t+1+j} = ∑_j a_j ρʲ ε_{t+1} = a(ρ) ε_{t+1}`. -/
theorem innov_PV {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    innov 𝔼 t (fun ω => ∑' j, ρ ^ j * s (t + 1 + j) ω) = gen a ρ • ε ((t : ℤ) + 1) := by
  rw [innov_PV_vec 𝔼 ((isMA_iff_vec a ε s).1 hs) (isMDSVec_of_isMDS 𝔼 hε)
    (fun k _ ω => hM k ω) hρ t]
  funext ω
  simp [dotShock, genVec]

/-- Cochrane (2023), eq. (4.2), p. 87, termwise scalar form valid for `|ρ| ≤ 1`:
`∑_j ρʲ Δ_{t+1} s_{t+1+j} = a(ρ) ε_{t+1}`. -/
theorem innov_PV_termwise {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ)
    (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) (gen a ρ * ε ((t : ℤ) + 1) ω) := by
  simp_rw [innov_MA 𝔼 hs hε hM, Pi.smul_apply, smul_eq_mul]
  have h := (summable_coeff_mul_pow hs.1 hρ).hasSum.mul_right (ε ((t : ℤ) + 1) ω)
  convert h using 1
  · funext j
    ring
  · rfl

/-- Cochrane (2023), eq. (4.2), p. 87: the innovations of a moving average vanish at long
horizons fast enough for transversality: `ρᵀ Δ_{t+1} s_{t+1+T} → 0` for `|ρ| ≤ 1`. -/
theorem tendsto_pow_mul_innov_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {s : ℕ → Ω → ℝ} (hs : IsMAVec a ε s) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * innov 𝔼 t (s (t + 1 + T)) ω) atTop (𝓝 0) := by
  simp_rw [innov_MAVec 𝔼 hs hε hM]
  have hterm : ∀ i, Tendsto (fun T => ρ ^ T * (a T i * ε ((t : ℤ) + 1) i ω)) atTop (𝓝 0) := by
    intro i
    have h0 : Tendsto (fun T => a T i) atTop (𝓝 0) := by
      have := (hs.1 i).tendsto_atTop_zero
      exact (tendsto_zero_iff_abs_tendsto_zero _).2 this
    have hb : Tendsto (fun T => a T i * ε ((t : ℤ) + 1) i ω) atTop (𝓝 0) := by
      simpa using h0.mul_const (ε ((t : ℤ) + 1) i ω)
    refine squeeze_zero_norm (fun T => ?_) ((tendsto_zero_iff_norm_tendsto_zero).1 hb)
    rw [norm_mul, norm_pow, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) hρ)
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun i _ => hterm i
  simp only [Finset.sum_const_zero] at h
  convert h using 1
  funext T
  simp [dotShock, Finset.mul_sum]

/-! ### The AR(1) and the i.i.d. process as moving averages -/

/-- Cochrane (2023), eq. (4.3), p. 87: a process with moving-average coefficients `a_j = ηʲ`
follows the AR(1) law `s_{t+1} = η s_t + ε_{t+1}`. -/
theorem ar1_of_MA {η : ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA (fun j => η ^ j) ε s)
    {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (t : ℕ) :
    s (t + 1) = η • s t + ε ((t : ℤ) + 1) := by
  funext ω
  have hsum : Summable fun j : ℕ => η ^ j * ε (((t + 1 : ℕ) : ℤ) - j) ω :=
    Summable.of_norm_bounded (hs.1.mul_right M) fun j => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)
  rw [hs.2 (t + 1) ω, hsum.tsum_eq_zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hs.2 t ω, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  rw [add_comm]
  congr 1
  · refine tsum_congr fun j => ?_
    rw [pow_succ]
    push_cast
    rw [show (t : ℤ) + 1 - (j + 1) = t - j by ring]
    ring

/-- Cochrane (2023), eq. (4.3), p. 87: conversely, for `|η| < 1` and a bounded shock, the
AR(1) started from its infinite past `s_0 = ∑ ηʲ ε_{−j}` has moving-average coefficients `ηʲ`. -/
theorem MA_of_ar1 {η : ℝ} (hη : |η| < 1) {ε : ℤ → Ω → ℝ} {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    {s : ℕ → Ω → ℝ} (h0 : ∀ ω, s 0 ω = ∑' j : ℕ, η ^ j * ε (-(j : ℤ)) ω)
    (hrec : ∀ t, s (t + 1) = η • s t + ε ((t : ℤ) + 1)) : IsMA (fun j => η ^ j) ε s := by
  have habs : Summable fun j => |η ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg η) hη
  refine ⟨habs, fun t => ?_⟩
  induction t with
  | zero => intro ω; simpa using h0 ω
  | succ t ih =>
    intro ω
    have hsum : Summable fun j : ℕ => η ^ j * ε (((t + 1 : ℕ) : ℤ) - j) ω :=
      Summable.of_norm_bounded (habs.mul_right M) fun j => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hM _ ω) (abs_nonneg _)
    rw [hrec t, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih ω, hsum.tsum_eq_zero_add,
      ← tsum_mul_left]
    simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
    rw [add_comm]
    congr 1
    · refine tsum_congr fun j => ?_
      rw [pow_succ]
      push_cast
      rw [show (t : ℤ) + 1 - (j + 1) = t - j by ring]
      ring

/-- Cochrane (2023), eq. (4.3), p. 87: a moving average with coefficients `ηʲ` in a
martingale-difference shock is an AR(1) in the sense of the core (`E_t s_{t+1} = η s_t`). -/
theorem isAR1_of_MA {η : ℝ} {ε : ℤ → Ω → ℝ} {s : ℕ → Ω → ℝ} (hs : IsMA (fun j => η ^ j) ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) : 𝔼.IsAR1 η s := by
  have had : 𝔼.Adapted s :=
    adapted_MAVec 𝔼 ((isMA_iff_vec _ ε s).1 hs) (isMDSVec_of_isMDS 𝔼 hε) fun k _ ω => hM k ω
  refine ⟨had, fun t => ?_⟩
  rw [ar1_of_MA hs hM t, map_add, map_smul, had t, hε.2 t, add_zero]

/-- Cochrane (2023), p. 88 ("θ = 0 gives an i.i.d. surplus process"): the coefficients
`a_0 = 1`, `a_j = 0` (`j ≥ 1`) of an i.i.d. (white-noise) process. -/
def iidCoeff (j : ℕ) : ℝ := if j = 0 then 1 else 0

/-- Cochrane (2023), p. 88: the shock itself, `s_t = ε_t`, is a moving average with the
i.i.d. coefficients. -/
theorem isMA_iid (ε : ℤ → Ω → ℝ) : IsMA iidCoeff ε (fun t => ε t) := by
  refine ⟨?_, fun t ω => ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    simp only [Finset.mem_singleton] at hj
    simp [iidCoeff, hj]
  · rw [tsum_eq_single 0 fun j hj => by simp [iidCoeff, hj]]
    simp [iidCoeff]

/-- Cochrane (2023), p. 88: the i.i.d. process has `a(z) = 1` for every `z`. -/
theorem gen_iid (z : ℝ) : gen iidCoeff z = 1 := by
  unfold gen
  rw [tsum_eq_single 0 fun j hj => by simp [iidCoeff, hj]]
  simp [iidCoeff]

/-! ### A genuinely random shock -/

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock of the core finite tree (`±1` at
dates 1 and 2, zero otherwise), indexed by `ℤ` with no pre-sample shocks. -/
noncomputable def coinShockZ : ℤ → Bool × Bool → ℝ := extendShock coinShock

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock is a martingale difference for the
coin-flip expectation system. -/
theorem coinShockZ_isMDS : IsMDS coinSystem coinShockZ := by
  refine isMDS_extendShock coinSystem ⟨fun t => ?_, coinShock_mean_zero⟩
  funext ω
  rw [coinSystem, FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun ω' h => coinShock_measurable t h

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock is bounded by one. -/
theorem coinShockZ_bounded (k : ℤ) (ω : Bool × Bool) : |coinShockZ k ω| ≤ 1 := by
  refine extendShock_bounded zero_le_one (fun t ω' => ?_) k ω
  unfold coinShock
  split_ifs <;> simp

/-- Cochrane (2023), eq. (4.1), p. 87: the coin-flip shock is genuinely random: `ε_1 = 1` after
heads. -/
theorem coinShockZ_one : coinShockZ 1 (true, true) = 1 := by
  simp [coinShockZ, extendShock, coinShock]

end Cochrane.DebtDeficitsInflation.Innovations
