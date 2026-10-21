/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.InvertibilityMeasureL2

/-!
# The Wold decomposition theorem

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4 and 2.1.6, pp. 597 and 600 ("an autoregression of this surplus
process recovers the Wold representation, which has an invertible moving average"; "if you do
run an autoregression you recover a representation that is invertible, by the Wold
decomposition theorem").

The book invokes the Wold decomposition theorem without stating it. This module proves it in full
for a weakly stationary sequence `(x_t)_{t ∈ ℤ}` in a real Hilbert space `H` (in `L²` this is the
space of second moments; inner products are covariances, orthogonal projections are best linear
forecasts). Stationarity is either covariance stationarity (`⟪x_s, x_u⟫` depends only on
`s − u`) or, equivalently (`stationary_iff_exists_shift`), `x` is the orbit of a linear isometry
`U` of `H`, `U x_t = x_{t+1}`.

## Main definitions

* `past x t`: `H_t`, the closed span of `x_t, x_{t−1}, …`; `remote x`: `H_{−∞} = ⋂_t H_t`.
* `innov x t`: the innovation `e_t = x_t − P_{H_{t−1}} x_t` (the one-step-ahead linear forecast
  error, the error of the infinite autoregression).
* `woldCoeff x j`: `c_j = ⟪x_0, e_{−j}⟫ / ‖e‖²`; `detPart x t`: `d_t = P_{H_{−∞}} x_t`.
* `Deterministic x`: `x_t ∈ H_{t−1}` for all `t`; `Regular x`: `H_{−∞} = 0`.

## Main results

* (a) `innov_mem`, `innov_mem_orthogonal`, `innov_whiteNoise`: `e_t ∈ H_t`, `e_t ⟂ H_{t−1}`,
  the `e_t` are orthogonal with constant norm.
* (b) `wold_decomposition`: `x_t = ∑_{j ≥ 0} c_j e_{t−j} + d_t`, the series converging in `H`,
  `∑ c_j² < ∞` (with Bessel's bound), `c_0 = 1` when `e ≠ 0`, `c_j = ⟪x_t, e_{t−j}⟫/‖e‖²` for
  every `t`, `d_t ∈ H_{−∞}`, `d ⟂ e`.
* (c) `wold_unique`: any representation `x_t = ∑ b_j w_{t−j} + z_t` with `w_t ∈ H_t`,
  `w_t ⟂ H_{t−1}`, `b_0 = 1`, `z_t ∈ H_{−∞}` is the Wold one.
* (d) `deterministic_iff`, `regular_iff`, `wold_dichotomy`: `x` is deterministic iff `e = 0` iff
  `d = x`; regular iff `d = 0`; in general the regular part `u_t = ∑ c_j e_{t−j}` is regular, the
  deterministic part `d` is deterministic (`H_{−∞}` is the closed span of `d_{t−1}, d_{t−2}, …`),
  both are stationary and they are uncorrelated. `mixed_example`: neither part can be dropped.
* Stationarity: `stationary_of_shift`, `exists_shift_of_stationary`, `wold_of_stationary`.
* Correction (A2 p. 597, "the Wold representation, which has an invertible moving average"):
  `wold_unit_root`, `IIDEconomy.coin_wold_unit_root` — the Wold moving average is fundamental
  but can have a root on the unit circle (`s_t = ε_t − ε_{t−1}`), and then no absolutely
  summable autoregression recovers the Wold innovation.
* Links: `maProc_regular` (every absolutely summable moving average in white noise is regular);
  `wold_factor_is_wold` (the factorised `InvertibilityMeasure.wold_factor`: its `w_t` is the
  Wold innovation, its fitted coefficients `ã = (1 − θ⁻¹L)g` are the Wold coefficients, and
  `d = 0`); `IIDEconomy.iid_wold`, `IIDEconomy.iid_wold_factor_is_wold`,
  `IIDEconomy.iid_mixed`, `IIDEconomy.coin_wold` in `L²(ν^ℕ)` of the i.i.d. economy of
  `InvertibilityMeasureL2` (the mixed example `x_t = ε_t + 1`: the mean is the deterministic
  part).
-/

namespace Cochrane.DebtDeficitsInflation.Wold

open Filter Topology
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The past, the remote past and the innovations -/

/-- Cochrane (2023), Online Appendix p. 597 (`E(s_t|s_{t−1}, s_{t−2}, …)`): `H_t`, the closed
linear span of `x_t, x_{t−1}, …` (the same subspace as `Invertibility.Hilbert.pastSpan`). -/
noncomputable abbrev past (x : ℤ → H) (t : ℤ) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range fun k : ℕ => x (t - k))).topologicalClosure

/-- Cochrane (2023), Online Appendix p. 597 (tool): `past` is `Invertibility.Hilbert.pastSpan`. -/
theorem past_eq_pastSpan (x : ℤ → H) (t : ℤ) : past x t = pastSpan x t := rfl

/-- Cochrane (2023), Online Appendix p. 600 (the Wold theorem): the remote past
`H_{−∞} = ⋂_t H_t` (written as its own closure, which `remote_eq` shows is no change). -/
noncomputable abbrev remote (x : ℤ → H) : Submodule ℝ H := (⨅ t, past x t).topologicalClosure

/-- Cochrane (2023), Online Appendix p. 597 ("`w_{s,t+1} = s_{t+1} − E(s_{t+1}|s_t, s_{t−1}, …)`"):
the Wold innovation `e_t = x_t − P_{H_{t−1}} x_t`, the one-step-ahead linear forecast error. -/
noncomputable def innov [CompleteSpace H] (x : ℤ → H) (t : ℤ) : H :=
  x t - (past x (t - 1)).starProjection (x t)

/-- Cochrane (2023), Online Appendix p. 600: the Wold coefficients
`c_j = ⟪x_0, e_{−j}⟫ / ‖e_0‖²` (`0` when `e = 0`). -/
noncomputable def woldCoeff [CompleteSpace H] (x : ℤ → H) (j : ℕ) : ℝ :=
  ⟪x 0, innov x (-j)⟫ / ‖innov x 0‖ ^ 2

/-- Cochrane (2023), Online Appendix p. 600: the deterministic part `d_t = P_{H_{−∞}} x_t`. -/
noncomputable def detPart [CompleteSpace H] (x : ℤ → H) (t : ℤ) : H :=
  (remote x).starProjection (x t)

/-- Cochrane (2023), Online Appendix p. 600: `x` is deterministic (perfectly linearly predictable
from its own past) if `x_t ∈ H_{t−1}` for every `t`. -/
def Deterministic (x : ℤ → H) : Prop := ∀ t, x t ∈ past x (t - 1)

/-- Cochrane (2023), Online Appendix p. 600: `x` is regular (purely non-deterministic) if its
remote past is trivial, `H_{−∞} = 0`. -/
def Regular (x : ℤ → H) : Prop := remote x = ⊥

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_{t−k} ∈ H_t`. -/
theorem mem_past (x : ℤ → H) (t : ℤ) (k : ℕ) : x (t - k) ∈ past x t :=
  mem_pastSpan_self x t k

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_t ∈ H_t`. -/
theorem self_mem_past (x : ℤ → H) (t : ℤ) : x t ∈ past x t := by
  simpa using mem_past x t 0

/-- Cochrane (2023), Online Appendix p. 597 (tool): `H_t` grows with `t`. -/
theorem past_mono (x : ℤ → H) {t t' : ℤ} (h : t ≤ t') : past x t ≤ past x t' :=
  pastSpan_mono x h

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_s ∈ H_t` for `s ≤ t`. -/
theorem mem_past_of_le (x : ℤ → H) {s t : ℤ} (h : s ≤ t) : x s ∈ past x t :=
  past_mono x h (self_mem_past x s)

/-- Cochrane (2023), Online Appendix p. 600 (tool): the remote past is closed, so it equals
`⋂_t H_t`. -/
theorem remote_eq (x : ℤ → H) : remote x = ⨅ t, past x t := by
  refine IsClosed.submodule_topologicalClosure_eq ?_
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun t => Submodule.isClosed_topologicalClosure _

/-- Cochrane (2023), Online Appendix p. 600 (tool): `H_{−∞} ≤ H_t`. -/
theorem remote_le (x : ℤ → H) (t : ℤ) : remote x ≤ past x t := by
  rw [remote_eq]; exact iInf_le _ t

/-- Cochrane (2023), Online Appendix p. 600 (tool): membership in `H_{−∞}`. -/
theorem mem_remote_iff {x : ℤ → H} {z : H} : z ∈ remote x ↔ ∀ t, z ∈ past x t := by
  rw [remote_eq, Submodule.mem_iInf]

variable [CompleteSpace H]

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): `e_t ∈ H_t`. -/
theorem innov_mem (x : ℤ → H) (t : ℤ) : innov x t ∈ past x t :=
  Submodule.sub_mem _ (self_mem_past x t)
    (past_mono x (by omega) (Submodule.starProjection_apply_mem _ _))

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): `e_t ⟂ H_{t−1}` (the forecast error is
uncorrelated with everything linear in the past). -/
theorem innov_mem_orthogonal (x : ℤ → H) (t : ℤ) : innov x t ∈ (past x (t - 1))ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

/-- Cochrane (2023), Online Appendix p. 597 (tool): `⟪e_t, y⟫ = 0` for `y ∈ H_{t−1}`. -/
theorem inner_innov_of_mem {x : ℤ → H} {t : ℤ} {y : H} (hy : y ∈ past x (t - 1)) :
    ⟪innov x t, y⟫ = 0 :=
  Submodule.inner_left_of_mem_orthogonal hy (innov_mem_orthogonal x t)

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): the innovations are orthogonal,
`⟪e_t, e_s⟫ = 0` for `s < t`. -/
theorem inner_innov_lt (x : ℤ → H) {s t : ℤ} (h : s < t) : ⟪innov x t, innov x s⟫ = 0 :=
  inner_innov_of_mem (past_mono x (by omega) (innov_mem x s))

/-- Cochrane (2023), Online Appendix p. 597 (tool): `x_t = e_t + P_{H_{t−1}} x_t`. -/
theorem x_eq_innov_add (x : ℤ → H) (t : ℤ) :
    x t = innov x t + (past x (t - 1)).starProjection (x t) := by
  rw [innov, sub_add_cancel]

/-- Cochrane (2023), Online Appendix p. 597 (tool): `e_t = 0` iff `x_t ∈ H_{t−1}`. -/
theorem innov_eq_zero_iff (x : ℤ → H) (t : ℤ) : innov x t = 0 ↔ x t ∈ past x (t - 1) := by
  rw [innov, sub_eq_zero, eq_comm, Submodule.starProjection_eq_self_iff]

/-- Cochrane (2023), Online Appendix p. 600 (tool, the key step of Wold's proof):
`H_t = H_{t−1} ⊕ span{e_t}`, in the form: an element of `H_t` orthogonal to `e_t` lies in
`H_{t−1}`. -/
theorem mem_past_pred {x : ℤ → H} {t : ℤ} {y : H} (hy : y ∈ past x t)
    (he : ⟪innov x t, y⟫ = 0) : y ∈ past x (t - 1) := by
  set K := past x (t - 1) with hK
  -- `Q = P_{Kᗮ}` maps `H_t` into the line through `e_t`
  have hcl : IsClosed (((ℝ ∙ innov x t).comap (Kᗮ.starProjection : H →ₗ[ℝ] H) : Set H)) := by
    rw [Submodule.comap_coe]
    exact (Submodule.closed_of_finiteDimensional (ℝ ∙ innov x t)).preimage
      Kᗮ.starProjection.continuous
  have hle : past x t ≤ (ℝ ∙ innov x t).comap (Kᗮ.starProjection : H →ₗ[ℝ] H) := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) hcl
    rintro _ ⟨k, rfl⟩
    change Kᗮ.starProjection (x (t - k)) ∈ ℝ ∙ innov x t
    rw [Submodule.starProjection_orthogonal_val]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [show t - ((0 : ℕ) : ℤ) = t by simp]
      exact Submodule.mem_span_singleton_self (innov x t)
    · have hmem : x (t - k) ∈ K := mem_past_of_le x (by omega)
      rw [(Submodule.starProjection_eq_self_iff).mpr hmem, sub_self]
      exact Submodule.zero_mem _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hle hy)
  change a • innov x t = Kᗮ.starProjection y at ha
  rw [Submodule.starProjection_orthogonal_val] at ha
  have h1 : ⟪innov x t, y - K.starProjection y⟫ = 0 := by
    rw [inner_sub_right, he, inner_innov_of_mem (Submodule.starProjection_apply_mem _ _),
      sub_zero]
  rw [← ha, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
  have h2 : a • innov x t = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h, zero_smul]
    · rw [norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h), smul_zero]
  rw [h2, eq_comm, sub_eq_zero] at ha
  rw [ha]
  exact Submodule.starProjection_apply_mem _ _

/-! ### Stationarity: the shift -/

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 597 (tool; stationarity): the shift `U` maps `H_t` into
`H_{t+1}`. -/
theorem map_past {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) {t : ℤ} {y : H}
    (hy : y ∈ past x t) : U y ∈ past x (t + 1) :=
  InvertibilityMeasure.map_pastSpan U.toContinuousLinearMap
    (fun k => by
      change U (x (t - k)) = x (t + 1 - k)
      rw [hU]; congr 1; ring) hy

/-- Cochrane (2023), Online Appendix p. 597 (tool): the shift commutes with the forecast,
`P_{H_t} x_{t+1} = U P_{H_{t−1}} x_t`. -/
theorem starProjection_shift {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : (past x t).starProjection (x (t + 1)) =
      U ((past x (t - 1)).starProjection (x t)) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · have := map_past hU (Submodule.starProjection_apply_mem (past x (t - 1)) (x t))
    rwa [sub_add_cancel] at this
  · rw [← hU, ← map_sub]
    refine mem_orthogonal_pastSpan fun k => ?_
    rw [show t - (k : ℤ) = t - 1 - k + 1 by ring, ← hU, LinearIsometry.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero _ _ (mem_past x (t - 1) k)

/-- Cochrane (2023), Online Appendix p. 597, Wold (a) (stationarity of the innovations):
`e_{t+1} = U e_t`. -/
theorem innov_shift {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    innov x (t + 1) = U (innov x t) := by
  have h : innov x (t + 1) = x (t + 1) - (past x t).starProjection (x (t + 1)) := by
    simp only [innov, add_sub_cancel_right]
  rw [h, starProjection_shift hU, ← hU, innov, map_sub]

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 597 (tool): inner products of two processes that the
same isometry shifts are shift invariant, `⟪y_{s+t}, z_{u+t}⟫ = ⟪y_s, z_u⟫`. -/
theorem inner_shift {U : H →ₗᵢ[ℝ] H} {y z : ℤ → H} (hy : ∀ t, U (y t) = y (t + 1))
    (hz : ∀ t, U (z t) = z (t + 1)) (s u t : ℤ) : ⟪y (s + t), z (u + t)⟫ = ⟪y s, z u⟫ := by
  induction t using Int.induction_on with
  | zero => simp
  | succ n ih => rw [← add_assoc, ← add_assoc, ← hy, ← hz, LinearIsometry.inner_map_map, ih]
  | pred n ih =>
    rw [← ih]
    have h1 : y (s + -(n : ℤ)) = U (y (s + (-(n : ℤ) - 1))) := by rw [hy]; congr 1; ring
    have h2 : z (u + -(n : ℤ)) = U (z (u + (-(n : ℤ) - 1))) := by rw [hz]; congr 1; ring
    rw [h1, h2, LinearIsometry.inner_map_map]

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): the innovations have constant norm. -/
theorem norm_innov {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    ‖innov x t‖ = ‖innov x 0‖ := by
  have hs : ∀ τ, U (innov x τ) = innov x (τ + 1) := fun τ => (innov_shift hU τ).symm
  have h := inner_shift hs hs 0 0 t
  rw [zero_add, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- Cochrane (2023), Online Appendix p. 597, Wold (a): the innovations are white noise with
variance `‖e_0‖²` (orthogonal, constant norm), in the sense of `Invertibility.Hilbert`. -/
theorem innov_whiteNoise {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    WhiteNoise (innov x) (‖innov x 0‖ ^ 2) := by
  intro t u
  rcases lt_trichotomy t u with h | h | h
  · rw [real_inner_comm, inner_innov_lt x h]
    simp [h.ne]
  · subst h
    simp [norm_innov hU]
  · rw [inner_innov_lt x h]
    simp [h.ne']

/-- Cochrane (2023), Online Appendix p. 600 (tool): if `e = 0` at one date it is `0` at all. -/
theorem innov_eq_zero_of {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (h0 : innov x 0 = 0) (t : ℤ) : innov x t = 0 := by
  rw [← norm_eq_zero, norm_innov hU, h0, norm_zero]

/-! ### The Wold coefficients and the regular part -/

/-- Cochrane (2023), Online Appendix p. 600 (tool): `c_j` does not depend on the date,
`⟪x_t, e_{t−j}⟫ = ⟪x_0, e_{−j}⟫`. -/
theorem inner_x_innov {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ)
    (j : ℕ) : ⟪x t, innov x (t - j)⟫ = ⟪x 0, innov x (-j)⟫ := by
  have h := inner_shift hU (fun τ => (innov_shift hU τ).symm) 0 (-j) t
  rwa [zero_add, show -(j : ℤ) + t = t - j by ring] at h

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): `c_j = ⟪x_t, e_{t−j}⟫ / ‖e_t‖²` at every
date `t`. -/
theorem woldCoeff_eq {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ)
    (j : ℕ) : woldCoeff x j = ⟪x t, innov x (t - j)⟫ / ‖innov x t‖ ^ 2 := by
  rw [woldCoeff, inner_x_innov hU, norm_innov hU t]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `⟪e_{t−j}, x_t⟫ = c_j ‖e‖²`. -/
theorem inner_innov_x {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ)
    (j : ℕ) : ⟪innov x (t - j), x t⟫ = woldCoeff x j * ‖innov x 0‖ ^ 2 := by
  by_cases h0 : innov x 0 = 0
  · rw [innov_eq_zero_of hU h0, inner_zero_left, h0, norm_zero]; ring
  · rw [woldCoeff, real_inner_comm, inner_x_innov hU, div_mul_cancel₀]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): `c_0 = 1` when `e ≠ 0`. -/
theorem woldCoeff_zero {x : ℤ → H} (h0 : innov x 0 ≠ 0) : woldCoeff x 0 = 1 := by
  have h : ⟪x 0, innov x 0⟫ = ‖innov x 0‖ ^ 2 := by
    rw [x_eq_innov_add x 0, inner_add_left, real_inner_self_eq_norm_sq, real_inner_comm,
      inner_innov_of_mem (Submodule.starProjection_apply_mem _ _), add_zero]
  rw [woldCoeff, Nat.cast_zero, neg_zero, h, div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))]

/-- Cochrane (2023), Online Appendix p. 600 (tool): the normalised innovations
`e_{t−j}/‖e‖`, `j ≥ 0`, are orthonormal. -/
theorem orthonormal_innov {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (h0 : innov x 0 ≠ 0) (t : ℤ) :
    Orthonormal ℝ (fun j : ℕ => ‖innov x 0‖⁻¹ • innov x (t - j)) := by
  have hn : ‖innov x 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [orthonormal_iff_ite]
  intro i j
  rw [real_inner_smul_left, real_inner_smul_right, innov_whiteNoise hU]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    field_simp
  · have : t - (i : ℤ) ≠ t - j := by omega
    simp [this, hij]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `c_j e_{t−j} = ⟪ê_j, x_t⟫ ê_j` with
`ê_j = e_{t−j}/‖e‖`. -/
theorem woldCoeff_smul {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (h0 : innov x 0 ≠ 0) (t : ℤ) (j : ℕ) :
    woldCoeff x j • innov x (t - j) =
      ⟪‖innov x 0‖⁻¹ • innov x (t - j), x t⟫ • (‖innov x 0‖⁻¹ • innov x (t - j)) := by
  have hn : ‖innov x 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [real_inner_smul_left, inner_innov_x hU, smul_smul]
  congr 1
  field_simp

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): the series `∑_{j ≥ 0} c_j e_{t−j}`
converges in `H` (to the regular part `maProc c e t`). -/
theorem hasSum_wold {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (maProc (woldCoeff x) (innov x) t) := by
  refine Summable.hasSum ?_
  by_cases h0 : innov x 0 = 0
  · simp only [innov_eq_zero_of hU h0, smul_zero]
    exact summable_zero
  · have hv := orthonormal_innov hU h0 t
    have hs := (hv.orthogonalFamily.summable_iff_norm_sq_summable
      (fun j => ⟪‖innov x 0‖⁻¹ • innov x (t - j), x t⟫)).mpr (hv.inner_products_summable (x t))
    refine hs.congr fun j => ?_
    rw [woldCoeff_smul hU h0 t j, LinearIsometry.toSpanSingleton_apply]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `‖⟪ê_j, x_0⟫‖² = ‖e‖² c_j²`. -/
theorem norm_inner_sq {x : ℤ → H} (h0 : innov x 0 ≠ 0) (j : ℕ) :
    ‖⟪‖innov x 0‖⁻¹ • innov x (0 - j), x 0⟫‖ ^ 2 = ‖innov x 0‖ ^ 2 * woldCoeff x j ^ 2 := by
  have hn : ‖innov x 0‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [Real.norm_eq_abs, sq_abs, real_inner_smul_left, zero_sub, real_inner_comm, woldCoeff]
  field_simp

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): `∑ c_j² < ∞`. -/
theorem summable_sq_woldCoeff {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Summable (fun j => woldCoeff x j ^ 2) := by
  by_cases h0 : innov x 0 = 0
  · simp [woldCoeff, h0]
  · have hv := orthonormal_innov hU h0 0
    have hn : ‖innov x 0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
    exact (summable_mul_left_iff hn).mp
      ((hv.inner_products_summable (x 0)).congr (norm_inner_sq h0))

/-- Cochrane (2023), Online Appendix p. 600, Wold (b) (Bessel's bound):
`‖e‖² ∑ c_j² ≤ ‖x_0‖²`. -/
theorem tsum_sq_woldCoeff_le {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    ‖innov x 0‖ ^ 2 * ∑' j, woldCoeff x j ^ 2 ≤ ‖x 0‖ ^ 2 := by
  by_cases h0 : innov x 0 = 0
  · rw [h0, norm_zero]; simp
  · have hv := orthonormal_innov hU h0 0
    calc ‖innov x 0‖ ^ 2 * ∑' j, woldCoeff x j ^ 2
        = ∑' j : ℕ, ‖innov x 0‖ ^ 2 * woldCoeff x j ^ 2 := tsum_mul_left.symm
      _ = ∑' j : ℕ, ‖⟪‖innov x 0‖⁻¹ • innov x (0 - j), x 0⟫‖ ^ 2 :=
          tsum_congr fun j => (norm_inner_sq h0 j).symm
      _ ≤ ‖x 0‖ ^ 2 := hv.tsum_inner_products_le (x 0)

/-- Cochrane (2023), Online Appendix p. 600 (tool): the regular part lies in `H_t`. -/
theorem regPart_mem {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    maProc (woldCoeff x) (innov x) t ∈ past x t :=
  hasSum_mem_pastSpan (hasSum_wold hU t) fun _ =>
    Submodule.smul_mem _ _ (past_mono x (by omega) (innov_mem x _))

/-- Cochrane (2023), Online Appendix p. 600 (tool): for any convergent series
`y = ∑ b_j e_{t−j}` in the innovations, `⟪e_{t−j}, y⟫ = b_j ‖e‖²`. -/
theorem inner_innov_hasSum {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    {t : ℤ} {b : ℕ → ℝ} {y : H} (h : HasSum (fun j : ℕ => b j • innov x (t - j)) y) (j : ℕ) :
    ⟪innov x (t - j), y⟫ = b j * ‖innov x 0‖ ^ 2 := by
  have hf : ∀ k : ℕ, ⟪innov x (t - j), b k • innov x (t - k)⟫ =
      if k = j then b j * ‖innov x 0‖ ^ 2 else 0 := by
    intro k
    rw [real_inner_smul_right, innov_whiteNoise hU]
    by_cases hk : k = j
    · subst hk; simp
    · have : t - (j : ℤ) ≠ t - k := by omega
      simp [this, hk]
  exact (inner_hasSum_right h (innov x (t - j))).unique ((hasSum_ite_eq j _).congr_fun hf)

/-- Cochrane (2023), Online Appendix p. 600 (tool): `e_s ⟂ H_{−∞}`. -/
theorem innov_mem_orthogonal_remote (x : ℤ → H) (s : ℤ) : innov x s ∈ (remote x)ᗮ :=
  Submodule.orthogonal_le (remote_le x (s - 1)) (innov_mem_orthogonal x s)

/-- Cochrane (2023), Online Appendix p. 600 (tool): the regular part is orthogonal to `H_{−∞}`. -/
theorem regPart_mem_orthogonal_remote {x : ℤ → H} {U : H →ₗᵢ[ℝ] H}
    (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    maProc (woldCoeff x) (innov x) t ∈ (remote x)ᗮ :=
  (Submodule.isClosed_orthogonal _).mem_of_tendsto (hasSum_wold hU t).tendsto_sum_nat
    (Eventually.of_forall fun _ => Submodule.sum_mem _ fun _ _ =>
      Submodule.smul_mem _ _ (innov_mem_orthogonal_remote x _))

/-- Cochrane (2023), Online Appendix p. 600 (the key step): `x_t − ∑ c_j e_{t−j}` lies in every
`H_s`, i.e. in `H_{−∞}`. -/
theorem sub_regPart_mem_remote {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : x t - maProc (woldCoeff x) (innov x) t ∈ remote x := by
  have hd0 : x t - maProc (woldCoeff x) (innov x) t ∈ past x t :=
    Submodule.sub_mem _ (self_mem_past x t) (regPart_mem hU t)
  have horth : ∀ s, ⟪innov x s, x t - maProc (woldCoeff x) (innov x) t⟫ = 0 := by
    intro s
    rcases le_or_gt s t with hs | hs
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, s = t - j := ⟨(t - s).toNat, by omega⟩
      rw [inner_sub_right, inner_innov_x hU, inner_innov_hasSum hU (hasSum_wold hU t), sub_self]
    · exact inner_innov_of_mem (past_mono x (by omega) hd0)
  have hmem : ∀ n : ℕ, x t - maProc (woldCoeff x) (innov x) t ∈ past x (t - n) := by
    intro n
    induction n with
    | zero => simpa using hd0
    | succ n ih =>
      have := mem_past_pred ih (horth _)
      rwa [show t - (n : ℤ) - 1 = t - ((n + 1 : ℕ) : ℤ) by push_cast; ring] at this
  rw [mem_remote_iff]
  intro s
  rcases le_or_gt s t with hs | hs
  · have := hmem (t - s).toNat
    rwa [show t - ((t - s).toNat : ℤ) = s by omega] at this
  · exact past_mono x hs.le hd0

/-- Cochrane (2023), Online Appendix p. 600, Wold (b): the deterministic part is
`d_t = P_{H_{−∞}} x_t = x_t − ∑ c_j e_{t−j}`. -/
theorem detPart_eq {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) (t : ℤ) :
    detPart x t = x t - maProc (woldCoeff x) (innov x) t :=
  Submodule.eq_starProjection_of_mem_orthogonal (sub_regPart_mem_remote hU t)
    (by rw [sub_sub_cancel]; exact regPart_mem_orthogonal_remote hU t)

/-- Cochrane (2023), Online Appendix p. 600 (tool): `x_t = u_t + d_t`. -/
theorem x_eq_regPart_add_detPart {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : x t = maProc (woldCoeff x) (innov x) t + detPart x t := by
  rw [detPart_eq hU, add_sub_cancel]

/-- Cochrane (2023), Online Appendix p. 600 (tool): `d_t ∈ H_{−∞}`. -/
theorem detPart_mem_remote (x : ℤ → H) (t : ℤ) : detPart x t ∈ remote x :=
  Submodule.starProjection_apply_mem _ _

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the Wold decomposition theorem** (the book
invokes it; here proved): let `x` be weakly stationary in a real Hilbert space, `U x_t = x_{t+1}`
for a linear isometry `U`; let `e_t = x_t − P_{H_{t−1}} x_t`.
(a) `e_t ∈ H_t`, `e_t ⟂ H_{t−1}`, and `e` is white noise (orthogonal, constant norm);
(b) `∑ c_j² < ∞` (indeed `‖e‖² ∑ c_j² ≤ ‖x_0‖²`), `c_0 = 1` if `e ≠ 0`,
`c_j = ⟪x_t, e_{t−j}⟫/‖e_t‖²` at every date, and `x_t = ∑_{j ≥ 0} c_j e_{t−j} + d_t` with the
series converging in `H`, `d_t = P_{H_{−∞}} x_t ∈ H_{−∞}` and `d ⟂ e`. -/
theorem wold_decomposition {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    (∀ t, innov x t ∈ past x t) ∧ (∀ t, innov x t ∈ (past x (t - 1))ᗮ) ∧
    WhiteNoise (innov x) (‖innov x 0‖ ^ 2) ∧
    Summable (fun j => woldCoeff x j ^ 2) ∧
    ‖innov x 0‖ ^ 2 * ∑' j, woldCoeff x j ^ 2 ≤ ‖x 0‖ ^ 2 ∧
    (innov x 0 ≠ 0 → woldCoeff x 0 = 1) ∧
    (∀ t (j : ℕ), woldCoeff x j = ⟪x t, innov x (t - j)⟫ / ‖innov x t‖ ^ 2) ∧
    (∀ t, HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (x t - detPart x t)) ∧
    (∀ t, detPart x t ∈ remote x) ∧
    (∀ s t, ⟪detPart x s, innov x t⟫ = 0) := by
  refine ⟨innov_mem x, innov_mem_orthogonal x, innov_whiteNoise hU, summable_sq_woldCoeff hU,
    tsum_sq_woldCoeff_le hU, woldCoeff_zero, woldCoeff_eq hU, fun t => ?_, detPart_mem_remote x,
    fun s t => ?_⟩
  · rw [detPart_eq hU, sub_sub_cancel]; exact hasSum_wold hU t
  · exact Submodule.inner_right_of_mem_orthogonal (detPart_mem_remote x s)
      (innov_mem_orthogonal_remote x t)

/-! ### Uniqueness -/

/-- Cochrane (2023), Online Appendix pp. 597 and 600, Wold (c), **uniqueness**: if
`x_t = ∑_{j ≥ 0} b_j w_{t−j} + z_t` (converging in `H`) with `w_t ∈ H_t`, `w_t ⟂ H_{t−1}`,
`b_0 = 1` and `z_t ∈ H_{−∞}`, then `w` is the Wold innovation, `z` the deterministic part, and
(when `e ≠ 0`) `b` the Wold coefficients. This is why "an autoregression recovers the Wold
representation": any one-sided representation in forecast errors is the Wold one. -/
theorem wold_unique {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) {w z : ℤ → H}
    {b : ℕ → ℝ} (hw : ∀ t, w t ∈ past x t) (hwo : ∀ t, w t ∈ (past x (t - 1))ᗮ)
    (hb0 : b 0 = 1) (hz : ∀ t, z t ∈ remote x)
    (hsum : ∀ t, HasSum (fun j : ℕ => b j • w (t - j)) (x t - z t)) :
    (∀ t, w t = innov x t) ∧ (∀ t, z t = detPart x t) ∧ (innov x 0 ≠ 0 → b = woldCoeff x) := by
  have hwe : ∀ t, w t = innov x t := by
    intro t
    have h1 := (hasSum_nat_add_iff' 1).mpr (hsum t)
    simp only [Finset.range_one, Finset.sum_singleton, hb0, one_smul, Nat.cast_zero,
      sub_zero] at h1
    have hmem : x t - z t - w t ∈ past x (t - 1) :=
      hasSum_mem_pastSpan h1 fun j => Submodule.smul_mem _ _ (past_mono x (by omega) (hw _))
    have hP : (past x (t - 1)).starProjection (x t) = x t - w t := by
      refine Submodule.eq_starProjection_of_mem_orthogonal ?_
        (by rw [sub_sub_cancel]; exact hwo t)
      have := Submodule.add_mem _ hmem (remote_le x (t - 1) (hz t))
      rwa [sub_right_comm, sub_add_cancel] at this
    rw [innov, hP, sub_sub_cancel]
  obtain rfl : w = innov x := funext hwe
  have hb : innov x 0 ≠ 0 → b = woldCoeff x := by
    intro h0
    funext j
    have h1 := inner_innov_hasSum hU (hsum 0) j
    have h2 : ⟪innov x (0 - j), z 0⟫ = 0 :=
      inner_innov_of_mem (remote_le x _ (hz 0))
    rw [inner_sub_right, h2, sub_zero, inner_innov_x hU] at h1
    exact (mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)) h1).symm
  refine ⟨hwe, fun t => ?_, hb⟩
  have hf : (fun j : ℕ => b j • innov x (t - j)) =
      fun j : ℕ => woldCoeff x j • innov x (t - j) := by
    funext j
    by_cases h0 : innov x 0 = 0
    · rw [innov_eq_zero_of hU h0, smul_zero, smul_zero]
    · rw [hb h0]
  have h := (hsum t).unique (hf ▸ (hasSum_wold hU t))
  rw [detPart_eq hU, ← h, sub_sub_cancel]

/-! ### The regular/deterministic dichotomy -/

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is deterministic iff its innovation
vanishes. -/
theorem deterministic_iff {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Deterministic x ↔ innov x 0 = 0 :=
  ⟨fun h => (innov_eq_zero_iff x 0).mpr (h 0),
    fun h t => (innov_eq_zero_iff x t).mp (innov_eq_zero_of hU h t)⟩

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is deterministic iff it equals its
deterministic part. -/
theorem deterministic_iff_detPart {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Deterministic x ↔ ∀ t, detPart x t = x t := by
  rw [deterministic_iff hU]
  constructor
  · intro h t
    rw [detPart_eq hU]
    simp [maProc, innov_eq_zero_of hU h]
  · intro h
    refine (innov_eq_zero_iff x 0).mpr ?_
    rw [← h 0]
    exact remote_le x _ (detPart_mem_remote x 0)

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is regular (`H_{−∞} = 0`) iff its
deterministic part vanishes. -/
theorem regular_iff {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Regular x ↔ ∀ t, detPart x t = 0 := by
  constructor
  · intro h t
    have hm := detPart_mem_remote x t
    rw [Regular] at h
    rwa [h, Submodule.mem_bot] at hm
  · intro h
    rw [Regular, Submodule.eq_bot_iff]
    intro z hz
    have hx : ∀ s, ⟪z, x s⟫ = 0 := by
      intro s
      rw [x_eq_regPart_add_detPart hU s, h s, add_zero]
      exact Submodule.inner_right_of_mem_orthogonal hz (regPart_mem_orthogonal_remote hU s)
    have h0 : z ∈ (past x 0)ᗮ := mem_orthogonal_pastSpan fun k => hx _
    exact inner_self_eq_zero.mp
      (Submodule.inner_right_of_mem_orthogonal (mem_remote_iff.mp hz 0) h0)

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): `x` is regular iff it is the moving
average of its innovations, `x_t = ∑ c_j e_{t−j}`. -/
theorem regular_iff_hasSum {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Regular x ↔ ∀ t, HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (x t) := by
  rw [regular_iff hU]
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · have := hasSum_wold hU t
    rwa [← sub_zero (x t), ← h, detPart_eq hU, sub_sub_cancel]
  · rw [detPart_eq hU, (hasSum_wold hU t).unique h, sub_self]

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 600 (tool): a closed subspace containing
`y_t, y_{t−1}, …` contains their closed span. -/
theorem past_le_of_mem {y : ℤ → H} {t : ℤ} {K : Submodule ℝ H} (hK : IsClosed (K : Set H))
    (h : ∀ k : ℕ, y (t - k) ∈ K) : past y t ≤ K :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact h k)) hK

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): the remote past is the closed span of the
deterministic part's past at any date, `H_{−∞} = closure span{d_t, d_{t−1}, …}`. -/
theorem remote_eq_past_detPart {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (t : ℤ) : remote x = past (detPart x) t := by
  have hle : past (detPart x) t ≤ remote x :=
    past_le_of_mem (Submodule.isClosed_topologicalClosure _)
      fun k => detPart_mem_remote x _
  refine le_antisymm (fun h hh => ?_) hle
  set D := past (detPart x) t
  set k := h - D.starProjection h with hk
  have hkr : k ∈ remote x :=
    Submodule.sub_mem _ hh (hle (Submodule.starProjection_apply_mem _ _))
  have hkD : k ∈ Dᗮ := Submodule.sub_starProjection_mem_orthogonal _
  have hkx : k ∈ (past x t)ᗮ := by
    refine mem_orthogonal_pastSpan fun j => ?_
    rw [x_eq_regPart_add_detPart hU, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal hkr (regPart_mem_orthogonal_remote hU _),
      zero_add]
    exact Submodule.inner_left_of_mem_orthogonal (mem_past (detPart x) t j) hkD
  have hk0 : k = 0 := inner_self_eq_zero.mp
    (Submodule.inner_right_of_mem_orthogonal (remote_le x t hkr) hkx)
  rw [hk, sub_eq_zero] at hk0
  rw [hk0]
  exact Submodule.starProjection_apply_mem _ _

/-- Cochrane (2023), Online Appendix p. 600, **Wold (d), the dichotomy**: the regular part
`u_t = ∑ c_j e_{t−j}` is regular, the deterministic part `d` is deterministic, `H_{−∞}` is
spanned by `d`'s past, `u` and `d` are uncorrelated at all dates, and both are stationary (shifted
by the same `U`). -/
theorem wold_dichotomy {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1)) :
    Regular (maProc (woldCoeff x) (innov x)) ∧ Deterministic (detPart x) ∧
    (∀ t, remote x = past (detPart x) t) ∧
    (∀ s t, ⟪maProc (woldCoeff x) (innov x) s, detPart x t⟫ = 0) ∧
    (∀ t, U (maProc (woldCoeff x) (innov x) t) = maProc (woldCoeff x) (innov x) (t + 1)) ∧
    (∀ t, U (detPart x t) = detPart x (t + 1)) := by
  set u := maProc (woldCoeff x) (innov x) with hu
  have hUu : ∀ t, U (u t) = u (t + 1) := by
    intro t
    have h := (hasSum_wold hU t).mapL U.toContinuousLinearMap
    refine h.unique ((hasSum_wold hU (t + 1)).congr_fun fun j => ?_)
    change U (woldCoeff x j • innov x (t - j)) = woldCoeff x j • innov x (t + 1 - j)
    rw [map_smul, ← innov_shift hU, show t - (j : ℤ) + 1 = t + 1 - j by ring]
  refine ⟨?_, fun t => ?_, remote_eq_past_detPart hU, fun s t => ?_, hUu, fun t => ?_⟩
  · -- the regular part is regular
    rw [Regular, Submodule.eq_bot_iff]
    intro z hz
    have hle : ∀ s, past u s ≤ past x s := fun s =>
      past_le_of_mem (Submodule.isClosed_topologicalClosure _)
        fun k => past_mono x (by omega) (regPart_mem hU _)
    have he : ∀ s, ⟪z, innov x s⟫ = 0 := fun s => by
      rw [real_inner_comm]
      exact inner_innov_of_mem (hle _ (mem_remote_iff.mp hz (s - 1)))
    have hzu : ∀ r, ⟪z, u r⟫ = 0 := fun r => by
      refine (inner_hasSum_right (hasSum_wold hU r) z).unique ?_
      convert hasSum_zero with j
      rw [real_inner_smul_right, he, mul_zero]
    exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal
      (mem_remote_iff.mp hz 0) (mem_orthogonal_pastSpan fun k => hzu _))
  · rw [← remote_eq_past_detPart hU]
    exact detPart_mem_remote x t
  · exact Submodule.inner_left_of_mem_orthogonal (detPart_mem_remote x t)
      (regPart_mem_orthogonal_remote hU s)
  · rw [detPart_eq hU, detPart_eq hU, map_sub, hU, ← hu, hUu]

/-- Cochrane (2023), Online Appendix p. 600, Wold (d): a process both regular and deterministic
is zero. -/
theorem eq_zero_of_regular_deterministic {x : ℤ → H} {U : H →ₗᵢ[ℝ] H}
    (hU : ∀ t, U (x t) = x (t + 1)) (hr : Regular x) (hd : Deterministic x) (t : ℤ) :
    x t = 0 := by
  rw [← (deterministic_iff_detPart hU).mp hd t, (regular_iff hU).mp hr t]

/-! ### Stationarity: covariance stationarity is the same as a shift isometry -/

omit [CompleteSpace H] in
/-- Cochrane (2023), Online Appendix p. 597 (stationarity): the orbit of a linear isometry is
covariance stationary, `⟪x_s, x_u⟫ = γ(s − u)` with `γ(k) = ⟪x_k, x_0⟫`. -/
theorem stationary_of_shift {x : ℤ → H} {U : H →ₗᵢ[ℝ] H} (hU : ∀ t, U (x t) = x (t + 1))
    (s u : ℤ) : ⟪x s, x u⟫ = ⟪x (s - u), x 0⟫ := by
  have := inner_shift hU hU (s - u) 0 u
  rwa [sub_add_cancel, zero_add] at this

/-- Cochrane (2023), Online Appendix p. 597 (stationarity): a covariance-stationary sequence
(`⟪x_s, x_u⟫` depends only on `s − u`) is the orbit of a linear isometry `U` of `H`,
`U x_t = x_{t+1}`: `U` is the isometric extension of `∑ c_t x_t ↦ ∑ c_t x_{t+1}` to the closed
span `K` of the `x_t`, and the identity on `Kᗮ`. -/
theorem exists_shift_of_stationary {x : ℤ → H} {γ : ℤ → ℝ}
    (hγ : ∀ s u, ⟪x s, x u⟫ = γ (s - u)) : ∃ U : H →ₗᵢ[ℝ] H, ∀ t, U (x t) = x (t + 1) := by
  classical
  set K : Submodule ℝ H := (Submodule.span ℝ (Set.range x)).topologicalClosure with hK
  set L : (ℤ →₀ ℝ) →ₗ[ℝ] H := Finsupp.linearCombination ℝ x with hL
  set L' : (ℤ →₀ ℝ) →ₗ[ℝ] H := Finsupp.linearCombination ℝ (fun t => x (t + 1)) with hL'
  have hspan : ∀ c, L c ∈ Submodule.span ℝ (Set.range x) := fun c => by
    rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ c
  have hspan' : ∀ c, L' c ∈ Submodule.span ℝ (Set.range x) := fun c => by
    have : L' c ∈ Submodule.span ℝ (Set.range fun t => x (t + 1)) := by
      rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ c
    exact Submodule.span_mono (by rintro _ ⟨t, rfl⟩; exact ⟨t + 1, rfl⟩) this
  let e : (ℤ →₀ ℝ) →ₗ[ℝ] K :=
    L.codRestrict K fun c => Submodule.le_topologicalClosure _ (hspan c)
  have hinner : ∀ c d : ℤ →₀ ℝ, ⟪L' c, L' d⟫ = ⟪L c, L d⟫ := by
    intro c d
    simp only [hL, hL', Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right, hγ, add_sub_add_right_eq_sub]
  have hnorm : ∀ c, ‖L' c‖ = ‖e c‖ := by
    intro c
    change ‖L' c‖ = ‖L c‖
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hinner]
  have hdense : DenseRange e := by
    refine Subtype.dense_iff.mpr ?_
    rw [← Set.range_comp]
    change (K : Set H) ⊆ closure (Set.range (L : (ℤ →₀ ℝ) → H))
    rw [← LinearMap.coe_range, hL, Finsupp.range_linearCombination, hK,
      Submodule.topologicalClosure_coe]
  let V : K →ₗᵢ[ℝ] H := L'.extendOfIsometry hdense hnorm
  have hVe : ∀ c, V (e c) = L' c := fun c => LinearMap.extendOfIsometry_eq L' hdense hnorm c
  have hVK : ∀ y : K, V y ∈ K := by
    intro y
    refine hdense.induction_on y ?_ fun c => ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage V.continuous
    · rw [hVe]; exact Submodule.le_topologicalClosure _ (hspan' c)
  let T : H →ₗ[ℝ] H := V.toLinearMap ∘ₗ (K.orthogonalProjectionOnto : H →ₗ[ℝ] K) +
    (LinearMap.id - (K.starProjection : H →ₗ[ℝ] H))
  have hT : ∀ y, T y = V (K.orthogonalProjectionOnto y) + (y - K.starProjection y) :=
    fun y => rfl
  have hPy : ∀ y, ((K.orthogonalProjectionOnto y : K) : H) = K.starProjection y := fun y => rfl
  refine ⟨⟨T, fun y => ?_⟩, fun t => ?_⟩
  · rw [hT]
    have h1 : ⟪V (K.orthogonalProjectionOnto y), y - K.starProjection y⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (hVK _)
        (Submodule.sub_starProjection_mem_orthogonal y)
    have h2 : ⟪K.starProjection y, y - K.starProjection y⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _)
        (Submodule.sub_starProjection_mem_orthogonal y)
    have e1 := norm_add_sq_eq_norm_sq_add_norm_sq_real h1
    have e2 := norm_add_sq_eq_norm_sq_add_norm_sq_real h2
    rw [add_sub_cancel] at e2
    have e3 : ‖V (K.orthogonalProjectionOnto y)‖ = ‖K.starProjection y‖ := by
      rw [LinearIsometry.norm_map]; rfl
    rw [e3, ← e2] at e1
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp e1
  · have hxK : x t ∈ K := Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩)
    change T (x t) = x (t + 1)
    rw [hT, (Submodule.starProjection_eq_self_iff).mpr hxK, sub_self, add_zero]
    have hP : K.orthogonalProjectionOnto (x t) = e (Finsupp.single t 1) := by
      apply Subtype.ext
      rw [hPy, (Submodule.starProjection_eq_self_iff).mpr hxK]
      change x t = L (Finsupp.single t 1)
      rw [hL, Finsupp.linearCombination_single, one_smul]
    rw [hP, hVe, hL', Finsupp.linearCombination_single, one_smul]

/-- Cochrane (2023), Online Appendix p. 597 (stationarity): the two notions of weak
stationarity agree — `⟪x_s, x_u⟫` depends only on `s − u` iff `x` is the orbit of a linear
isometry of `H`. -/
theorem stationary_iff_exists_shift (x : ℤ → H) :
    (∃ γ : ℤ → ℝ, ∀ s u, ⟪x s, x u⟫ = γ (s - u)) ↔
      ∃ U : H →ₗᵢ[ℝ] H, ∀ t, U (x t) = x (t + 1) :=
  ⟨fun ⟨_, hγ⟩ => exists_shift_of_stationary hγ,
    fun ⟨_, hU⟩ => ⟨fun k => ⟪x k, x 0⟫, stationary_of_shift hU⟩⟩

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the Wold decomposition for a
covariance-stationary sequence**: innovations are white noise, `∑ c_j² < ∞`, `c_0 = 1` if
`e ≠ 0`, `x_t = ∑ c_j e_{t−j} + d_t` in `H` with `d_t ∈ H_{−∞}`, `d ⟂ e`, the regular part is
regular and the deterministic part deterministic. -/
theorem wold_of_stationary {x : ℤ → H} {γ : ℤ → ℝ} (hγ : ∀ s u, ⟪x s, x u⟫ = γ (s - u)) :
    WhiteNoise (innov x) (‖innov x 0‖ ^ 2) ∧ Summable (fun j => woldCoeff x j ^ 2) ∧
    (innov x 0 ≠ 0 → woldCoeff x 0 = 1) ∧
    (∀ t, HasSum (fun j : ℕ => woldCoeff x j • innov x (t - j)) (x t - detPart x t)) ∧
    (∀ t, detPart x t ∈ remote x) ∧ (∀ s t, ⟪detPart x s, innov x t⟫ = 0) ∧
    Regular (maProc (woldCoeff x) (innov x)) ∧ Deterministic (detPart x) := by
  obtain ⟨U, hU⟩ := exists_shift_of_stationary hγ
  obtain ⟨-, -, h1, h2, -, h3, -, h4, h5, h6⟩ := wold_decomposition hU
  obtain ⟨h7, h8, -⟩ := wold_dichotomy hU
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ### Neither part can be dropped: a mixed process -/

/-- Cochrane (2023), Online Appendix p. 600, Wold (d), **a mixed example**: white noise plus a
fixed vector orthogonal to it, `x_t = ε_t + v` with `v ≠ 0`, `v ⟂ ε`. Its Wold innovation is
`ε`, its coefficients are `c = (1, 0, 0, …)`, its deterministic part is `d_t = v` (a mean, in
`L²`), and it is neither regular nor deterministic. -/
theorem mixed_example {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {v : H}
    (hv : v ≠ 0) (hve : ∀ t, ⟪e t, v⟫ = 0) {x : ℤ → H} (hx : ∀ t, x t = e t + v) :
    (∀ t, innov x t = e t) ∧ (∀ t, detPart x t = v) ∧
    (∀ j, woldCoeff x j = if j = 0 then 1 else 0) ∧ ¬ Regular x ∧ ¬ Deterministic x := by
  have hγ : ∀ s u, ⟪x s, x u⟫ = (fun k : ℤ => (if k = 0 then σ2 else 0) + ‖v‖ ^ 2) (s - u) := by
    intro s u
    rw [hx, hx, inner_add_left, inner_add_right, inner_add_right, he, hve, real_inner_comm,
      hve, real_inner_self_eq_norm_sq]
    simp only [sub_eq_zero, add_zero, zero_add]
  obtain ⟨U, hU⟩ := exists_shift_of_stationary (x := x)
    (γ := fun k : ℤ => (if k = 0 then σ2 else 0) + ‖v‖ ^ 2) hγ
  -- `v` lies in every `H_s` (Cesàro means of the past)
  have hvmem : ∀ s, v ∈ past x s := by
    intro s
    set y : ℕ → H := fun n => ((n : ℝ) + 1)⁻¹ • ∑ m ∈ Finset.range (n + 1), x (s - m) with hy
    have hymem : ∀ n, y n ∈ past x s := fun n =>
      Submodule.smul_mem _ _ (Submodule.sum_mem _ fun m _ => mem_past x s m)
    have hdiff : ∀ n, y n - v =
        ((n : ℝ) + 1)⁻¹ • ∑ m ∈ Finset.range (n + 1), (1 : ℝ) • e (s - m) := by
      intro n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      simp only [hy, hx, one_smul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      rw [smul_add, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one,
        inv_mul_cancel₀ hn, one_smul, add_sub_cancel_right]
    have hnorm : ∀ n, ‖y n - v‖ ^ 2 = σ2 / ((n : ℝ) + 1) := by
      intro n
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      rw [hdiff, ← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right,
        InvertibilityMeasure.inner_sum_e he (fun _ => 1) (fun m => s - m)
          (fun m m' h => by simpa using h) (n + 1)]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      push_cast
      field_simp
    have hlim : Tendsto y atTop (𝓝 v) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h1 : Tendsto (fun n : ℕ => σ2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat σ2 |>.comp (tendsto_add_atTop_nat 1) |>.congr
          fun n => by simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h2
      refine h2.congr fun n => ?_
      simp only [Function.comp_apply]
      rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hlim
      (Eventually.of_forall hymem)
  have hw : ∀ t, e t ∈ past x t := fun t => by
    have : e t = x t - v := by rw [hx, add_sub_cancel_right]
    rw [this]
    exact Submodule.sub_mem _ (self_mem_past x t) (hvmem t)
  have hwo : ∀ t, e t ∈ (past x (t - 1))ᗮ := fun t => mem_orthogonal_pastSpan fun k => by
    have : t ≠ t - 1 - k := by omega
    rw [hx, inner_add_right, he, hve]
    simp [this]
  have hsum : ∀ t, HasSum (fun j : ℕ => (if j = 0 then (1 : ℝ) else 0) • e (t - j)) (x t - v) := by
    intro t
    rw [hx, add_sub_cancel_right]
    convert hasSum_single (f := fun j : ℕ => (if j = 0 then (1 : ℝ) else 0) • e (t - j)) 0
      (fun j hj => by simp [hj]) using 1
    simp
  obtain ⟨h1, h2, h3⟩ := wold_unique hU hw hwo (by simp) (fun _ => mem_remote_iff.mpr hvmem)
    hsum
  have h0 : innov x 0 ≠ 0 := by
    rw [← h1 0]
    intro h
    have := he 0 0
    rw [h, inner_zero_left] at this
    simp only [↓reduceIte] at this
    exact hσ this.symm
  refine ⟨fun t => (h1 t).symm, fun t => (h2 t).symm, fun j => (congrFun (h3 h0) j).symm,
    fun hr => hv ?_, fun hd => h0 ((deterministic_iff hU).mp hd)⟩
  rw [h2 0]
  exact (regular_iff hU).mp hr 0

/-! ### Links: moving averages, and the factorised Wold statement -/

/-- Cochrane (2023), Online Appendix p. 597 (tool): an absolutely summable moving average in white
noise with `σ² ≠ 0` is stationary — the shift of the shocks shifts it. -/
theorem maProc_shift {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {a : ℕ → ℝ}
    (ha : Summable (fun k => |a k|)) :
    ∃ U : H →ₗᵢ[ℝ] H, ∀ t, U (maProc a e t) = maProc a e (t + 1) := by
  obtain ⟨U, hU⟩ := InvertibilityMeasure.exists_shift he hσ
  refine ⟨U.toLinearIsometry, fun t => ?_⟩
  have h := (maProc_hasSum he ha t).mapL U.toLinearIsometry.toContinuousLinearMap
  refine h.unique ((maProc_hasSum he ha (t + 1)).congr_fun fun k => ?_)
  change U (a k • e (t - k)) = a k • e (t + 1 - k)
  rw [map_smul, hU, show t - (k : ℤ) + 1 = t + 1 - k by ring]

/-- Cochrane (2023), Online Appendix p. 597 ("the Wold representation, which has an invertible
moving average"): every absolutely summable moving average `s_t = ∑ a_k e_{t−k}` in white noise is
regular — its remote past is `0`, so its deterministic part vanishes and it is the moving average
of its own Wold innovations. -/
theorem maProc_regular {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) {a : ℕ → ℝ}
    (ha : Summable (fun k => |a k|)) : Regular (maProc a e) := by
  rw [Regular, Submodule.eq_bot_iff]
  intro z hz
  have he0 : ∀ r, ⟪z, e r⟫ = 0 := by
    intro r
    have horth : e r ∈ (past (maProc a e) (r - 1))ᗮ := mem_orthogonal_pastSpan fun k => by
      rw [InvertibilityMeasure.inner_e_maProc_int he ha]
      have : ¬ r ≤ r - 1 - k := by omega
      simp only [this, ↓reduceIte]
    exact Submodule.inner_right_of_mem_orthogonal (mem_remote_iff.mp hz (r - 1)) horth
  have hzs : ∀ q, ⟪z, maProc a e q⟫ = 0 := fun q => by
    refine (inner_hasSum_right (maProc_hasSum he ha q) z).unique ?_
    convert hasSum_zero with k
    rw [real_inner_smul_right, he0, mul_zero]
  exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal
    (mem_remote_iff.mp hz 0) (mem_orthogonal_pastSpan fun k => hzs _))

/-- Cochrane (2023), Online Appendix pp. 597 and 600, **the factorised statement is an instance of
Wold**: for `s_t = a(L)e_t` with `a(L) = (1 − θL)g(L)`, `|θ| > 1`, `g₀ = 1`, `g` invertible
(`InvertibilityMeasure.wold_factor`), the abstract Wold innovation of `s` is the autoregression
error `w_t = ∑ θ⁻ᵏ(e_{t−k} − θe_{t−k−1})`, the abstract Wold coefficients are the fitted
`ã = (1 − θ⁻¹L)g` (the flipped root), `‖w‖² = θ²σ²`, the deterministic part is `0` and `s` is
regular. -/
theorem wold_factor_is_wold {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {θ : ℝ}
    (hθ : 1 < |θ|) {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1)
    (hrec : Invertibility.Recoverable g) :
    (∀ t, innov (maProc (InvertibilityMeasure.factorCoeff θ g) e) t =
      woldInnov θ (maOne θ e) t) ∧
    woldCoeff (maProc (InvertibilityMeasure.factorCoeff θ g) e) =
      InvertibilityMeasure.factorCoeff θ⁻¹ g ∧
    (∀ t, detPart (maProc (InvertibilityMeasure.factorCoeff θ g) e) t = 0) ∧
    Regular (maProc (InvertibilityMeasure.factorCoeff θ g) e) ∧
    ‖innov (maProc (InvertibilityMeasure.factorCoeff θ g) e) 0‖ ^ 2 = θ ^ 2 * σ2 := by
  set s := maProc (InvertibilityMeasure.factorCoeff θ g) e with hs
  obtain ⟨U, hU⟩ := maProc_shift he hσ (InvertibilityMeasure.summable_factorCoeff θ hg)
  have hW := InvertibilityMeasure.wold_factor he hσ hθ hg hg0 hrec
  have hw : ∀ t, innov s t = woldInnov θ (maOne θ e) t := by
    intro t
    have hP : (past s (t - 1)).starProjection (s t) = s t - woldInnov θ (maOne θ e) t :=
      (hW t).1
    rw [innov, hP, sub_sub_cancel]
  have hn : ‖innov s 0‖ ^ 2 = θ ^ 2 * σ2 := by
    rw [hw, ← real_inner_self_eq_norm_sq]
    exact (hW 0).2.1
  have h0 : innov s 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    have hθ0 : θ ≠ 0 := by intro h'; rw [h', abs_zero] at hθ; linarith
    exact mul_ne_zero (pow_ne_zero 2 hθ0) hσ (by rw [← hn]; ring)
  obtain ⟨-, h2, h3⟩ := wold_unique hU (w := woldInnov θ (maOne θ e))
    (b := InvertibilityMeasure.factorCoeff θ⁻¹ g) (z := fun _ => 0)
    (fun t => by rw [← hw t]; exact innov_mem s t)
    (fun t => by rw [← hw t]; exact innov_mem_orthogonal s t) hg0
    (fun _ => Submodule.zero_mem _) (fun t => by rw [sub_zero]; exact (hW t).2.2.2.1)
  exact ⟨hw, (h3 h0).symm, fun t => (h2 t).symm, (regular_iff hU).mpr fun t => (h2 t).symm, hn⟩

/-- Cochrane (2023), Online Appendix p. 597 ("the Wold representation, which has an invertible
moving average"), **correction**: the Wold moving average is fundamental (`e_t ∈ H_t`) but need not
be invertible. For `s_t = e_t − ρe_{t−1}` with `ρ = ±1`, the Wold innovation is the structural
shock, the Wold coefficients are `(1, −ρ, 0, …)`, so the Wold polynomial vanishes at `ρ` on the
unit circle, and no absolutely summable autoregression of current and past `s` converges to the
Wold innovation. -/
theorem wold_unit_root {e : ℤ → H} {σ2 : ℝ} (he : WhiteNoise e σ2) (hσ : σ2 ≠ 0) {ρ : ℝ}
    (hρ : ρ ^ 2 = 1) :
    (∀ t, innov (maProc (Invertibility.armaCoeff 0 ρ) e) t = e t) ∧
    woldCoeff (maProc (Invertibility.armaCoeff 0 ρ) e) = Invertibility.armaCoeff 0 ρ ∧
    Regular (maProc (Invertibility.armaCoeff 0 ρ) e) ∧
    Innovations.gen (woldCoeff (maProc (Invertibility.armaCoeff 0 ρ) e)) ρ = 0 ∧ |ρ| = 1 ∧
    ∀ t, ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (Invertibility.armaCoeff 0 ρ) e (t - k))
        (innov (maProc (Invertibility.armaCoeff 0 ρ) e) t) := by
  set s := maProc (Invertibility.armaCoeff 0 ρ) e with hs
  have ha := Invertibility.summable_abs_armaCoeff (show |(0 : ℝ)| < 1 by simp) ρ
  obtain ⟨U, hU⟩ := maProc_shift he hσ ha
  have habs : |ρ| = 1 := by
    have : |ρ| ^ 2 = 1 := by rw [sq_abs, hρ]
    nlinarith [abs_nonneg ρ]
  have hroot : Innovations.gen (Invertibility.armaCoeff 0 ρ) ρ = 0 := by
    rw [Invertibility.ma1_aRho]; nlinarith
  have hwo : ∀ t, e t ∈ (past s (t - 1))ᗮ := fun t => mem_orthogonal_pastSpan fun k => by
    rw [InvertibilityMeasure.inner_e_maProc_int he ha]
    have : ¬ t ≤ t - 1 - k := by omega
    simp only [this, ↓reduceIte]
  obtain ⟨h1, h2, h3⟩ := wold_unique hU (w := e) (b := Invertibility.armaCoeff 0 ρ)
    (z := fun _ => 0) (fun t => (InvertibilityMeasure.mem_pastSpan_unit_root he hρ t).2) hwo
    rfl (fun _ => Submodule.zero_mem _)
    (fun t => by rw [sub_zero]; exact maProc_hasSum he ha t)
  have h0 : innov s 0 ≠ 0 := by
    rw [← h1 0]
    intro h
    have := he 0 0
    rw [h, inner_zero_left] at this
    simp only [↓reduceIte] at this
    exact hσ this.symm
  have hc := (h3 h0).symm
  have hroot' : Innovations.gen (woldCoeff s) ρ = 0 := by rw [hc]; exact hroot
  refine ⟨fun t => (h1 t).symm, hc, (regular_iff hU).mpr fun t => (h2 t).symm, hroot', habs,
    fun t => ?_⟩
  rw [← h1 t]
  exact InvertibilityMeasure.not_filter_of_aRho_eq_zero he hσ ha habs.le hroot t

/-! ### The i.i.d. economy in `L²(ν^ℕ)` -/

namespace IIDEconomy

open MeasureTheory ProbabilityTheory
open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID
open Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2

/-- Cochrane (2023), Online Appendix p. 600 (the deterministic part as a mean): the constant
random variable `1` in `L²(ν^ℕ)`. -/
noncomputable def oneL2 (ν : ProbabilityMeasure ℝ) : Lp ℝ 2 (iidSystem ν).μ :=
  (memLp_const (1 : ℝ)).toLp _

/-- Cochrane (2023), Online Appendix p. 600 (tool): `E[1 · 1] = 1`. -/
theorem inner_oneL2 (ν : ProbabilityMeasure ℝ) : ⟪oneL2 ν, oneL2 ν⟫ = 1 := by
  rw [L2.inner_def]
  have h2 : (oneL2 ν : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  have hc : (fun ω => ⟪(oneL2 ν : (ℕ → ℝ) → ℝ) ω, (oneL2 ν : (ℕ → ℝ) → ℝ) ω⟫)
      =ᵐ[(iidSystem ν).μ] fun _ => (1 : ℝ) := by
    filter_upwards [h2] with ω e2
    rw [e2]
    simp
  rw [integral_congr_ae hc]
  simp

/-- Cochrane (2023), Online Appendix p. 600 (tool): `1 ≠ 0` in `L²(ν^ℕ)`. -/
theorem oneL2_ne_zero (ν : ProbabilityMeasure ℝ) : oneL2 ν ≠ 0 := by
  intro h
  have := inner_oneL2 ν
  rw [h, inner_zero_left] at this
  exact zero_ne_one this

/-- Cochrane (2023), Online Appendix p. 600 (tool): mean-zero shocks are uncorrelated with the
constant, `E[ε_t · 1] = 0`. -/
theorem inner_shockL2_one {ν : ProbabilityMeasure ℝ} {B : ℝ}
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (t : ℤ) :
    ⟪shockL2 hbdd t, oneL2 ν⟫ = 0 := by
  rw [L2.inner_def]
  have h1 : (shockL2 hbdd t : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ]
      fun ω => ω (Equiv.intEquivNat t) := MemLp.coeFn_toLp _
  have h2 : (oneL2 ν : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  have hc : (fun ω => ⟪(shockL2 hbdd t : (ℕ → ℝ) → ℝ) ω, (oneL2 ν : (ℕ → ℝ) → ℝ) ω⟫)
      =ᵐ[(iidSystem ν).μ] fun ω => ω (Equiv.intEquivNat t) := by
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]
    simp
  rw [integral_congr_ae hc]
  have h := integral_shock_fun ν (Equiv.intEquivNat t) (f := id) measurable_id
  simp only [id] at h
  rw [h, hmean]

/-- Cochrane (2023), p. 102 and Online Appendix pp. 597 and 600, the Wold theorem in `L²` of the
i.i.d. economy: every absolutely summable moving average of the i.i.d. shocks is regular and is
the moving average `∑ c_j e_{t−j}` (converging in mean square) of its own Wold innovations, which
are white noise, with `∑ c_j² < ∞` and `c_0 = 1`. -/
theorem iid_wold {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) :
    WhiteNoise (innov (maProc a (shockL2 hbdd))) (‖innov (maProc a (shockL2 hbdd)) 0‖ ^ 2) ∧
    Summable (fun j => woldCoeff (maProc a (shockL2 hbdd)) j ^ 2) ∧
    (innov (maProc a (shockL2 hbdd)) 0 ≠ 0 → woldCoeff (maProc a (shockL2 hbdd)) 0 = 1) ∧
    Regular (maProc a (shockL2 hbdd)) ∧
    ∀ t, HasSum (fun j : ℕ => woldCoeff (maProc a (shockL2 hbdd)) j •
      innov (maProc a (shockL2 hbdd)) (t - j)) (maProc a (shockL2 hbdd) t) := by
  have he := iid_whiteNoise hmean hvar hbdd
  obtain ⟨U, hU⟩ := maProc_shift he hσ.ne' ha
  have hr := maProc_regular he ha
  obtain ⟨-, -, h1, h2, -, h3, -⟩ := wold_decomposition hU
  exact ⟨h1, h2, h3, hr, (regular_iff_hasSum hU).mp hr⟩

/-- Cochrane (2023), Online Appendix pp. 597 and 600, in `L²` of the i.i.d. economy: for
`a(L) = (1 − θL)g(L)` (`|θ| > 1`, `g₀ = 1`, `g` invertible) the Wold innovation of the surplus is
the autoregression error `w` (not the structural shock), the Wold coefficients are the fitted
`ã = (1 − θ⁻¹L)g`, the Wold innovation variance is `θ²σ²`, and the surplus is regular. -/
theorem iid_wold_factor_is_wold {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {θ : ℝ} (hθ : 1 < |θ|)
    {g : ℕ → ℝ} (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1)
    (hrec : Invertibility.Recoverable g) :
    (∀ t, innov (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) t =
      woldInnov θ (maOne θ (shockL2 hbdd)) t) ∧
    woldCoeff (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) =
      InvertibilityMeasure.factorCoeff θ⁻¹ g ∧
    Regular (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) ∧
    ‖innov (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) 0‖ ^ 2 =
      θ ^ 2 * σ2 ∧
    innov (maProc (InvertibilityMeasure.factorCoeff θ g) (shockL2 hbdd)) 0 ≠ shockL2 hbdd 0 := by
  obtain ⟨h1, h2, -, h4, h5⟩ :=
    wold_factor_is_wold (iid_whiteNoise hmean hvar hbdd) hσ.ne' hθ hg hg0 hrec
  refine ⟨h1, h2, h4, h5, ?_⟩
  rw [h1]
  exact (iid_wold_factor hmean hvar hσ hbdd hθ hg hg0 hrec 0).2.2.2.2.2

/-- Cochrane (2023), Online Appendix p. 600, Wold (d), a mixed process in `L²` of the i.i.d.
economy: `x_t = ε_t + 1` (shocks with a nonzero mean). Its Wold innovation is `ε_t`, its
coefficients are `(1, 0, 0, …)`, its deterministic part is the mean `1`, and it is neither regular
nor deterministic. -/
theorem iid_mixed {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {x : ℤ → Lp ℝ 2 (iidSystem ν).μ}
    (hx : ∀ t, x t = shockL2 hbdd t + oneL2 ν) :
    (∀ t, innov x t = shockL2 hbdd t) ∧ (∀ t, detPart x t = oneL2 ν) ∧
    (∀ j, woldCoeff x j = if j = 0 then 1 else 0) ∧ ¬ Regular x ∧ ¬ Deterministic x :=
  mixed_example (iid_whiteNoise hmean hvar hbdd) hσ.ne' (oneL2_ne_zero ν)
    (inner_shockL2_one hbdd hmean) hx

/-- Cochrane (2023), Online Appendix pp. 597 and 600, the fair coin (`σ² = 1`, on the
non-finitely-supported `{±1}^ℕ`): for `|ρ| < 1`, the MA(1) `s_t = e_t − ρ⁻¹e_{t−1}` (`a(ρ) = 0`)
has Wold innovation variance `ρ⁻²`, Wold coefficients `(1, −ρ, 0, 0, …)` (the root flipped to
`ρ`), and is regular; `ε_t + 1` is a mixed process with deterministic part `1`. -/
theorem coin_wold {ρ : ℝ} (hρ0 : 0 < |ρ|) (hρ : |ρ| < 1) :
    woldCoeff (maProc (InvertibilityMeasure.factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
      (shockL2 coin_bdd)) = InvertibilityMeasure.factorCoeff ρ (fun k => if k = 0 then 1 else 0) ∧
    InvertibilityMeasure.factorCoeff ρ (fun k => if k = 0 then 1 else 0) 1 = -ρ ∧
    Regular (maProc (InvertibilityMeasure.factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
      (shockL2 coin_bdd)) ∧
    ‖innov (maProc (InvertibilityMeasure.factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
      (shockL2 coin_bdd)) 0‖ ^ 2 = (ρ⁻¹) ^ 2 * 1 ∧
    (∀ t, detPart (fun t => shockL2 coin_bdd t + oneL2 coin) t = oneL2 coin) := by
  have hθ : 1 < |ρ⁻¹| := by rw [abs_inv]; exact one_lt_inv_iff₀.mpr ⟨hρ0, hρ⟩
  have hδ : Summable (fun k : ℕ => |(if k = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  obtain ⟨-, h2, h3, h4, -⟩ := iid_wold_factor_is_wold coin_mean coin_var one_pos coin_bdd hθ hδ
    (by simp) InvertibilityMeasure.recoverable_delta
  obtain ⟨-, h5, -⟩ := iid_mixed coin_mean coin_var one_pos coin_bdd (x := fun t =>
    shockL2 coin_bdd t + oneL2 coin) fun _ => rfl
  refine ⟨by rwa [inv_inv] at h2, by simp [InvertibilityMeasure.factorCoeff], h3, h4, h5⟩

/-- Cochrane (2023), Online Appendix p. 597, **correction** in `L²` of the fair-coin economy: the
surplus `s_t = ε_t − ε_{t−1}` has Wold innovation `ε_t` and Wold polynomial `1 − z`, with a root at
`z = 1` on the unit circle; no absolutely summable autoregression recovers the Wold innovation. -/
theorem coin_wold_unit_root (t : ℤ) :
    innov (maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd)) t = shockL2 coin_bdd t ∧
    Innovations.gen (woldCoeff (maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd))) 1 = 0 ∧
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd) (t - k))
        (innov (maProc (Invertibility.armaCoeff 0 1) (shockL2 coin_bdd)) t) := by
  obtain ⟨h1, -, -, h4, -, h6⟩ := wold_unit_root (iid_whiteNoise coin_mean coin_var coin_bdd)
    one_ne_zero (ρ := 1) (by norm_num)
  exact ⟨h1 t, h4, h6 t⟩

end IIDEconomy

end Cochrane.DebtDeficitsInflation.Wold
