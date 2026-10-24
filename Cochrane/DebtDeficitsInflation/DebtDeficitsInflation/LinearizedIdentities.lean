/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.Innovations

/-!
# The linearised government-debt identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.5, eqs. (3.17)–(3.25),
pp. 63–68, as used in Chapter 4 (pp. 86–98), proved here for this project.

The primitives are the linearised flow identity (3.17)
`ρ v_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` (with `r = rⁿ − π`) and the linearised
geometric-maturity bond-return identity of Online Appendix §1.3, `rⁿ_{t+1} = ω q_{t+1} − q_t`
(`q` the log bond price). Both are stated as exact equalities between random variables at every
date (they hold ex post). The derivation of these two first-order approximations from the
nonlinear model, as exact derivatives, is in `LinearizationDerivation`; here every claim the book
derives FROM them is proved exactly, for an arbitrary `ExpectationSystem`.

Infinite sums whose convergence the book merely assumes ("assuming that the sums converge")
are expressed with `SeriesTo f a` (the partial sums of `∑ f_j` converge to `a`, i.e. ordinary
convergence, which does not require absolute summability); `tsum` corollaries are given under
summability, and an `E_t`-of-`tsum` version for bounded processes.

## Main results

* `Recursion`, `rec_finite`, `rec_map_finite`, `rec_seriesTo_map`: forward iteration of
  `x_t = ρ x_{t+1} + f_{t+1}` and of any linear image of it (`E_m`, `Δ_{t+1}`), with the
  terminal condition as an explicit limit; `tvc_of_bound`, `tvc_E_of_bounded`,
  `tvc_innov_of_bounded`, `tvc_innov_of_MAVec`: sufficient conditions for it.
* `Flow` (3.17), `sOfFlow`, `flow_sOfFlow` (p. 66 / p. 86: inferring `s̃` from the identity makes
  it hold exactly), `pv_finite` (3.18), `pv_expected`, `pv_expected_tsum`,
  `pv_expected_bounded` (3.19).
* `unexpected_inflation_identity` (3.20), `BondReturn`, `bond_return_identity` (3.21),
  `weighted_inflation_identity` (3.22), and under constant expected returns
  (`ConstExpReturn`) and no growth: `weighted_inflation_identity_const` (3.23),
  `inflation_identity_const` (3.24), `bond_return_identity_const` (3.25); one-period debt:
  `inflation_identity_one_period` (p. 67) and `inflation_identity_one_period_const` (p. 66).
-/

namespace Cochrane.DebtDeficitsInflation.LinearizedIdentities

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Ordinary convergence of series -/

/-- Cochrane (2023), eq. (3.19), p. 64 ("assuming that the sums converge"): the series
`∑_{j ≥ 0} f_j` converges (its partial sums tend) to `a`. -/
def SeriesTo (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun T => ∑ j ∈ Finset.range T, f j) atTop (𝓝 a)

/-- Cochrane (2023), eq. (3.19), p. 64: an unconditionally convergent series converges. -/
theorem seriesTo_of_hasSum {f : ℕ → ℝ} {a : ℝ} (h : HasSum f a) : SeriesTo f a :=
  h.tendsto_sum_nat

/-- Cochrane (2023), eq. (3.19), p. 64: for a summable series both notions of sum agree. -/
theorem seriesTo_iff_hasSum {f : ℕ → ℝ} {a : ℝ} (hf : Summable f) : SeriesTo f a ↔ HasSum f a :=
  (hf.hasSum_iff_tendsto_nat).symm

/-- Cochrane (2023), eq. (3.19), p. 64: the limit of a convergent series is unique. -/
theorem SeriesTo.unique {f : ℕ → ℝ} {a b : ℝ} (ha : SeriesTo f a) (hb : SeriesTo f b) : a = b :=
  tendsto_nhds_unique ha hb

/-- Cochrane (2023), eq. (3.19), p. 64: termwise equal series have the same limit. -/
theorem SeriesTo.congr {f g : ℕ → ℝ} {a b : ℝ} (h : SeriesTo f a) (hfg : ∀ j, f j = g j)
    (hab : a = b) : SeriesTo g b := by
  subst hab
  unfold SeriesTo at h ⊢
  simp_rw [← hfg]
  exact h

/-- Cochrane (2023), eq. (3.19), p. 64: convergent series add. -/
theorem SeriesTo.add {f g : ℕ → ℝ} {a b : ℝ} (hf : SeriesTo f a) (hg : SeriesTo g b) :
    SeriesTo (fun j => f j + g j) (a + b) := by
  unfold SeriesTo at hf hg ⊢
  simp_rw [Finset.sum_add_distrib]
  exact hf.add hg

/-- Cochrane (2023), eq. (3.19), p. 64: convergent series subtract. -/
theorem SeriesTo.sub {f g : ℕ → ℝ} {a b : ℝ} (hf : SeriesTo f a) (hg : SeriesTo g b) :
    SeriesTo (fun j => f j - g j) (a - b) := by
  unfold SeriesTo at hf hg ⊢
  simp_rw [Finset.sum_sub_distrib]
  exact hf.sub hg

/-- Cochrane (2023), eq. (3.19), p. 64: a convergent series may be scaled. -/
theorem SeriesTo.const_mul {f : ℕ → ℝ} {a : ℝ} (hf : SeriesTo f a) (c : ℝ) :
    SeriesTo (fun j => c * f j) (c * a) := by
  unfold SeriesTo at hf ⊢
  simp_rw [← Finset.mul_sum]
  exact hf.const_mul c

/-- Cochrane (2023), eq. (3.19), p. 64: the zero series converges to zero. -/
theorem seriesTo_zero : SeriesTo (fun _ => 0) 0 := by
  unfold SeriesTo
  simp

/-- Cochrane (2023), eq. (3.20), p. 65 (the sums `∑_{j ≥ 1}`): dropping the first term,
`∑_{j ≥ 0} f_j = a` iff `∑_{j ≥ 0} f_{j+1} = a − f_0`. -/
theorem seriesTo_succ_iff {f : ℕ → ℝ} {a : ℝ} :
    SeriesTo f a ↔ SeriesTo (fun j => f (j + 1)) (a - f 0) := by
  unfold SeriesTo
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [Finset.sum_range_succ']
  constructor
  · intro h
    simpa using h.sub_const (f 0)
  · intro h
    simpa using h.add_const (f 0)

/-! ### Forward iteration of a valuation recursion -/

/-- Cochrane (2023), eq. (3.17), p. 63: the valuation recursion `x_t = ρ x_{t+1} + f_{t+1}`
(the flow identity, the Campbell–Shiller identity and the bond-price identity all have this
form). -/
def Recursion (ρ : ℝ) (x f : ℕ → Ω → ℝ) : Prop := ∀ t, x t = ρ • x (t + 1) + f (t + 1)

/-- Cochrane (2023), eq. (3.18), p. 63: forward iteration,
`x_t = ∑_{j<T} ρʲ f_{t+1+j} + ρᵀ x_{t+T}` (holds ex post). -/
theorem rec_finite {ρ : ℝ} {x f : ℕ → Ω → ℝ} (h : Recursion ρ x f) (t T : ℕ) :
    x t = ∑ j ∈ Finset.range T, ρ ^ j • f (t + 1 + j) + ρ ^ T • x (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hx := h (t + T)
    rw [show t + T + 1 = t + (T + 1) by omega] at hx
    rw [ih, hx, Finset.sum_range_succ, smul_add, smul_smul, ← pow_succ,
      show t + 1 + T = t + (T + 1) by omega]
    abel

/-- Cochrane (2023), eq. (3.18), p. 63 ("holds ex post, so it holds ex ante"): any linear map
(e.g. `E_m` or `Δ_{t+1}`) applied to the forward iteration. -/
theorem rec_map_finite (L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (h : Recursion ρ x f) (t T : ℕ) :
    L (x t) = ∑ j ∈ Finset.range T, ρ ^ j • L (f (t + 1 + j)) + ρ ^ T • L (x (t + T)) := by
  conv_lhs => rw [rec_finite h t T]
  rw [map_add, map_sum, map_smul]
  simp_rw [map_smul]

/-- Cochrane (2023), eq. (3.19), p. 64: if the terminal term `ρᵀ L x_{t+T}` vanishes, the
linear image of the forward iteration converges: `L x_t = ∑_{j ≥ 0} ρʲ L f_{t+1+j}`. -/
theorem rec_seriesTo_map (L : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)) {ρ : ℝ} {x f : ℕ → Ω → ℝ}
    (h : Recursion ρ x f) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * L (x (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * L (f (t + 1 + j)) ω) (L (x t) ω) := by
  have hS : ∀ T, ∑ j ∈ Finset.range T, ρ ^ j * L (f (t + 1 + j)) ω =
      L (x t) ω - ρ ^ T * L (x (t + T)) ω := by
    intro T
    have := congrFun (rec_map_finite L h t T) ω
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  unfold SeriesTo
  simp_rw [hS]
  simpa using (tendsto_const_nhds (x := L (x t) ω)).sub hT

/-- Cochrane (2023), eq. (3.19), p. 64 ("the debt-to-GDP ratio is expected to grow no faster
than `ρ⁻ᵗ`"): for `|ρ| < 1` a bounded sequence satisfies the terminal condition
`ρᵀ y_T → 0`. -/
theorem tvc_of_bound {ρ : ℝ} (hρ : |ρ| < 1) {y : ℕ → ℝ} {K : ℝ} (hy : ∀ T, |y T| ≤ K) :
    Tendsto (fun T => ρ ^ T * y T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℕ => |ρ| ^ T * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const K
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hy T) (pow_nonneg (abs_nonneg _) T)

/-- Cochrane (2023), eq. (3.19), p. 64: for `|ρ| < 1` a bounded process satisfies the
terminal condition `ρᵀ E_m x_{t+T} → 0`. -/
theorem tvc_E_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (m t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * 𝔼.E m (x (t + T)) ω) atTop (𝓝 0) :=
  tvc_of_bound hρ fun T => 𝔼.abs_E_le (hx (t + T)) m ω

/-- Cochrane (2023), eq. (3.20), p. 65: for `|ρ| < 1` a bounded process satisfies the
innovation terminal condition `ρᵀ Δ_{s+1} x_{t+T} → 0`. -/
theorem tvc_innov_of_bounded {ρ : ℝ} (hρ : |ρ| < 1) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x t ω| ≤ M) (s t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * innov 𝔼 s (x (t + T)) ω) atTop (𝓝 0) :=
  tvc_of_bound hρ (K := M + M) fun T => by
    rw [innov_apply, Pi.sub_apply]
    exact (abs_sub _ _).trans
      (add_le_add (𝔼.abs_E_le (hx _) _ ω) (𝔼.abs_E_le (hx _) _ ω))

/-- Cochrane (2023), A2 §2.3, p. 606 ("imposing convergence of the last term"): a process with
an absolutely summable moving-average representation satisfies the innovation terminal
condition `ρᵀ Δ_{t+1} x_{t+T} → 0` for every `|ρ| ≤ 1` (including `ρ = 1`). -/
theorem tvc_innov_of_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : IsMAVec a ε x) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ρ ^ T * innov 𝔼 t (x (t + T)) ω) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have h := (tendsto_pow_mul_innov_MAVec 𝔼 hx hε hM hρ t ω).const_mul ρ
  rw [mul_zero] at h
  refine h.congr fun T => ?_
  rw [pow_succ, show t + (T + 1) = t + 1 + T by omega]
  ring

/-! ### The flow identity and the present value -/

/-- Cochrane (2023), eq. (3.17), p. 63: the linearised flow identity
`ρ v_{t+1} = v_t + r_{t+1} − g_{t+1} − s̃_{t+1}` at every date. -/
def Flow (ρ : ℝ) (v r g s : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t + r (t + 1) - g (t + 1) - s (t + 1)

/-- Cochrane (2023), eq. (3.17), p. 63: the flow identity is the valuation recursion with
payoff `s̃ + g − r`. -/
theorem flow_iff_recursion (ρ : ℝ) (v r g s : ℕ → Ω → ℝ) :
    Flow ρ v r g s ↔ Recursion ρ v (fun t => s t + g t - r t) := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> funext ω <;> have := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Cochrane (2023), p. 66 and §4.1, p. 86: the surplus inferred from the linearised flow
identity, `s̃_{t+1} := v_t + r_{t+1} − g_{t+1} − ρ v_{t+1}` (the date-0 value is irrelevant). -/
def sOfFlow (ρ : ℝ) (v r g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => v t + r (t + 1) - g (t + 1) - ρ • v (t + 1)

/-- Cochrane (2023), p. 66 and §4.1, p. 86: "I infer the surplus from the linearized flow
identity (3.17), so that linearized identities hold exactly". -/
theorem flow_sOfFlow (ρ : ℝ) (v r g : ℕ → Ω → ℝ) : Flow ρ v r g (sOfFlow ρ v r g) := by
  intro t
  simp only [sOfFlow]
  abel

/-- Cochrane (2023), p. 66 and §4.1, p. 86: the inferred surplus is the only one consistent
with the flow identity. -/
theorem eq_sOfFlow {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (t : ℕ) :
    s (t + 1) = sOfFlow ρ v r g (t + 1) := by
  simp only [sOfFlow]
  rw [h t]
  abel

/-- Cochrane (2023), eq. (3.18), p. 63: the ex-post present-value identity
`v_t = ∑_{j<T} ρʲ s̃_{t+1+j} + ∑_{j<T} ρʲ g_{t+1+j} − ∑_{j<T} ρʲ r_{t+1+j} + ρᵀ v_{t+T}`. -/
theorem pv_finite {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (t T : ℕ) :
    v t = ∑ j ∈ Finset.range T, ρ ^ j • s (t + 1 + j) +
      ∑ j ∈ Finset.range T, ρ ^ j • g (t + 1 + j) -
      ∑ j ∈ Finset.range T, ρ ^ j • r (t + 1 + j) + ρ ^ T • v (t + T) := by
  rw [rec_finite ((flow_iff_recursion ρ v r g s).1 h) t T]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Cochrane (2023), eq. (3.19), p. 64, combined form: under the terminal condition
`E_t ρᵀ v_{t+T} → 0`, `v_t = ∑_{j ≥ 0} ρʲ E_t (s̃ + g − r)_{t+1+j}`. -/
theorem pv_expected_combined {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (v t ω) := by
  have h0 := rec_seriesTo_map (𝔼.E t) ((flow_iff_recursion ρ v r g s).1 h) hT
  rwa [hv t] at h0

/-- Cochrane (2023), eq. (3.19), p. 64: under the terminal condition, if the surplus and growth
present values converge (to `S`, `G`), so does the discount-rate term, to `S + G − v_t`; i.e.
`v_t = E_t ∑ ρʲ s̃_{t+1+j} + E_t ∑ ρʲ g_{t+1+j} − E_t ∑ ρʲ r_{t+1+j}`. -/
theorem pv_expected {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (hv : 𝔼.Adapted v)
    {t : ℕ} {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0))
    {S G : ℝ} (hS : SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * 𝔼.E t (g (t + 1 + j)) ω) G) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) (S + G - v t ω) := by
  refine ((hS.add hG).sub (pv_expected_combined 𝔼 h hv hT)).congr (fun j => ?_) rfl
  simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]
  ring

/-- Cochrane (2023), eq. (3.19), p. 64, `tsum` form: when the three present values are
summable, `v_t = ∑ ρʲ E_t s̃_{t+1+j} + ∑ ρʲ E_t g_{t+1+j} − ∑ ρʲ E_t r_{t+1+j}`. -/
theorem pv_expected_tsum {ρ : ℝ} {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω)
    (hg : Summable fun j => ρ ^ j * 𝔼.E t (g (t + 1 + j)) ω)
    (hr : Summable fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) :
    v t ω = ∑' j, ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω + ∑' j, ρ ^ j * 𝔼.E t (g (t + 1 + j)) ω -
      ∑' j, ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω := by
  have h1 := pv_expected 𝔼 h hv hT (seriesTo_of_hasSum hs.hasSum) (seriesTo_of_hasSum hg.hasSum)
  have h2 := (seriesTo_of_hasSum hr.hasSum).unique h1
  linarith

/-- Cochrane (2023), eq. (3.19), p. 64, literal form `v_t = E_t ∑_{j ≥ 1} ρ^{j−1}(s̃ + g − r)_{t+j}`
for bounded processes and `|ρ| < 1` (the expectation of the infinite sum; the terminal
condition then holds automatically). -/
theorem pv_expected_bounded {ρ : ℝ} (hρ : |ρ| < 1) {v r g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼.Adapted v) {M : ℝ} (hvb : ∀ t ω, |v t ω| ≤ M)
    {K : ℝ} (hfb : ∀ t ω, |s t ω + g t ω - r t ω| ≤ K) (t : ℕ) :
    v t = 𝔼.E t (fun ω => ∑' j, ρ ^ j * (s (t + 1 + j) ω + g (t + 1 + j) ω -
      r (t + 1 + j) ω)) := by
  funext ω
  have hgeo : Summable fun j => |ρ ^ j| := by
    simpa [abs_pow] using summable_geometric_of_lt_one (abs_nonneg ρ) hρ
  rw [E_tsum_abs 𝔼 hgeo (x := fun j ω' => s (t + 1 + j) ω' + g (t + 1 + j) ω' -
    r (t + 1 + j) ω') (fun j ω' => hfb _ ω') t ω]
  have hser := pv_expected_combined 𝔼 h hv (tvc_E_of_bounded 𝔼 hρ hvb t t ω)
  have hsum := summable_E_terms 𝔼 hgeo (x := fun j ω' => s (t + 1 + j) ω' +
    g (t + 1 + j) ω' - r (t + 1 + j) ω') (fun j ω' => hfb _ ω') t ω
  refine (seriesTo_of_hasSum hsum.hasSum).unique (hser.congr (fun j => ?_) rfl) |>.symm
  rfl

/-! ### Innovation identities -/

/-- Cochrane (2023), eq. (3.20), p. 65 (unexpected-inflation identity): with
`r = rⁿ − π`, `v_t` known at `t` and the innovation terminal condition
`ρᵀ Δ_{t+1} v_{t+T} → 0`, if the surplus and growth innovation sums converge to `S` and `G`,
then `∑_{j ≥ 1} ρʲ Δ_{t+1} r_{t+1+j}` converges to `Δ_{t+1}π_{t+1} − Δ_{t+1}rⁿ_{t+1} + S + G`,
i.e. `Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`. -/
theorem unexpected_inflation_identity {ρ : ℝ} {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) {t : ℕ} (hv : 𝔼.E t (v t) = v t)
    {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S G : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω) G) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω)
      (innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω + S + G) := by
  have h0 := rec_seriesTo_map (innov 𝔼 t) ((flow_iff_recursion ρ v r g s).1 h) hT
  rw [innov_of_known 𝔼 hv] at h0
  have hR : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (r (t + 1 + j)) ω) (S + G - 0) := by
    refine ((hS.add hG).sub h0).congr (fun j => ?_) rfl
    simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]
    ring
  refine (seriesTo_succ_iff.1 hR).congr (fun j => ?_) ?_
  · rw [show t + 1 + (j + 1) = t + 2 + j by omega]
  · simp only [pow_zero, one_mul, add_zero, sub_zero]
    rw [hr (t + 1), map_sub, Pi.sub_apply]
    ring

/-- Cochrane (2023), eq. (3.20), p. 65, `tsum` form under summability:
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`. -/
theorem unexpected_inflation_identity_tsum {ρ : ℝ} {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) {t : ℕ} (hv : 𝔼.E t (v t) = v t)
    {ω : Ω} (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
    (hg : Summable fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω)
    (hrs : Summable fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω - ∑' j, ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω +
        ∑' j, ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω := by
  have h1 := unexpected_inflation_identity 𝔼 h hr hv hT (seriesTo_of_hasSum hs.hasSum)
    (seriesTo_of_hasSum hg.hasSum)
  have h2 := (seriesTo_of_hasSum hrs.hasSum).unique h1
  linarith

/-- Cochrane (2023), eq. (3.21), p. 65 and Online Appendix §1.3: the linearised return on a
geometric-maturity portfolio, `rⁿ_{t+1} = ω q_{t+1} − q_t` (`q` the log bond price, `ω` the
maturity decay). -/
def BondReturn (om : ℝ) (q rn : ℕ → Ω → ℝ) : Prop := ∀ t, rn (t + 1) = om • q (t + 1) - q t

/-- Cochrane (2023), eq. (3.21), p. 65: with `q` known at each date and the terminal condition
`ωᵀ Δ_{t+1} q_{t+1+T} → 0`, `Δ_{t+1} rⁿ_{t+1} = −∑_{j ≥ 1} ωʲ Δ_{t+1} rⁿ_{t+1+j}`. -/
theorem bond_return_identity {om : ℝ} {q rn : ℕ → Ω → ℝ} (hb : BondReturn om q rn)
    {t : ℕ} (hq : 𝔼.E t (q t) = q t) {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j)) ω)
      (-innov 𝔼 t (rn (t + 1)) ω) := by
  have hrec : Recursion om q (fun t => -rn t) := fun t => by
    funext ω
    have := congrFun (hb t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  have h0 := (rec_seriesTo_map (innov 𝔼 t) hrec hT).const_mul (-om)
  have hrn : innov 𝔼 t (rn (t + 1)) = om • innov 𝔼 t (q (t + 1)) := by
    rw [hb t, map_sub, map_smul, innov_of_known 𝔼 hq, sub_zero]
  refine h0.congr (fun j => ?_) ?_
  · rw [show t + 1 + 1 + j = t + 2 + j by omega, map_neg, Pi.neg_apply, pow_succ]
    ring
  · rw [hrn, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), eq. (3.21), p. 65, second equality: in terms of real returns and
inflation, `Δ_{t+1} rⁿ_{t+1} = −∑_{j ≥ 1} ωʲ Δ_{t+1}[r_{t+1+j} + π_{t+1+j}]`. -/
theorem bond_return_identity_real {om : ℝ} {q rn r infl : ℕ → Ω → ℝ}
    (hb : BondReturn om q rn) (hr : ∀ t, r t = rn t - infl t) {t : ℕ}
    (hq : 𝔼.E t (q t) = q t) {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ (j + 1) *
        (innov 𝔼 t (r (t + 2 + j)) ω + innov 𝔼 t (infl (t + 2 + j)) ω))
      (-innov 𝔼 t (rn (t + 1)) ω) := by
  refine (bond_return_identity 𝔼 hb hq hT).congr (fun j => ?_) rfl
  rw [hr, map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), p. 65 ("with one-period debt `ω = 0`, `rⁿ_{t+1} = i_t` and is known ahead
of time"): with `ω = 0` the nominal return has no innovation. -/
theorem one_period_innov_rn {q rn : ℕ → Ω → ℝ} (hb : BondReturn 0 q rn) (hq : 𝔼.Adapted q)
    (t : ℕ) : innov 𝔼 t (rn (t + 1)) = 0 := by
  rw [hb t, zero_smul, zero_sub, map_neg, innov_of_known 𝔼 (hq t), neg_zero]

/-- Cochrane (2023), eq. (3.22), p. 65 (weighted unexpected-inflation identity): combining
(3.20) and (3.21), if `∑_{j≥0} ωʲ Δ_{t+1}π_{t+1+j}` converges to `P` and the surplus and growth
sums to `S`, `G`, then `∑_{j≥1}(ρʲ − ωʲ)Δ_{t+1}r_{t+1+j}` converges to `P + S + G`, i.e.
`∑ ωʲΔπ_{t+1+j} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}(ρʲ − ωʲ)Δr_{t+1+j}`. -/
theorem weighted_inflation_identity {ρ om : ℝ} {v r rn infl g s q : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hb : BondReturn om q rn)
    (hv : 𝔼.Adapted v) (hq : 𝔼.Adapted q) {t : ℕ} {ω : Ω}
    (hTv : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    (hTq : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0))
    {S G P : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω) G)
    (hP : SeriesTo (fun j => om ^ j * innov 𝔼 t (infl (t + 1 + j)) ω) P) :
    SeriesTo (fun j => (ρ ^ (j + 1) - om ^ (j + 1)) * innov 𝔼 t (r (t + 2 + j)) ω)
      (P + S + G) := by
  have h1 := unexpected_inflation_identity 𝔼 h hr (hv t) hTv hS hG
  have h2 := bond_return_identity_real 𝔼 hb hr (hq t) hTq
  have h3 : SeriesTo (fun j => om ^ (j + 1) * innov 𝔼 t (infl (t + 2 + j)) ω)
      (P - innov 𝔼 t (infl (t + 1)) ω) := by
    refine (seriesTo_succ_iff.1 hP).congr (fun j => ?_) ?_
    · rw [show t + 1 + (j + 1) = t + 2 + j by omega]
    · simp
  refine (h1.sub (h2.sub h3)).congr (fun j => ?_) (by ring)
  ring

/-- Cochrane (2023), p. 66 (constant expected returns): `E_t r_{t+1} = c` at every date. -/
def ConstExpReturn (r : ℕ → Ω → ℝ) (c : ℝ) : Prop := ∀ t, 𝔼.E t (r (t + 1)) = fun _ => c

/-- Cochrane (2023), p. 66: with constant expected returns there is no news about future
returns, `Δ_{t+1} r_{t+1+j} = 0` for `j ≥ 1`. -/
theorem innov_future_return_zero {r : ℕ → Ω → ℝ} {c : ℝ} (hc : ConstExpReturn 𝔼 r c)
    (t j : ℕ) : innov 𝔼 t (r (t + 2 + j)) = 0 := by
  have h1 : 𝔼.E (t + 1) (r (t + 2 + j)) = fun _ => c := by
    rw [show t + 2 + j = t + 1 + j + 1 by omega, ← 𝔼.tower (Nat.le_add_right (t + 1) j),
      hc, 𝔼.const]
  have h2 : 𝔼.E t (r (t + 2 + j)) = fun _ => c := by
    rw [show t + 2 + j = t + 1 + j + 1 by omega, ← 𝔼.tower (show t ≤ t + 1 + j by omega),
      hc, 𝔼.const]
  rw [innov_apply, h1, h2, sub_self]

/-- Cochrane (2023), eq. (3.24), p. 68: with constant expected returns and no growth,
`Δ_{t+1}π_{t+1} − Δ_{t+1}rⁿ_{t+1} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`. -/
theorem inflation_identity_const {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t)
    (hc : ConstExpReturn 𝔼 r c) (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S) :
    innov 𝔼 t (infl (t + 1)) ω - innov 𝔼 t (rn (t + 1)) ω = -S := by
  have hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp) rfl
  have h1 := unexpected_inflation_identity 𝔼 h hr (hv t) hT hS hG
  have h0 : SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp [innov_future_return_zero 𝔼 hc]) rfl
  have := h0.unique h1
  linarith

/-- Cochrane (2023), eq. (3.25), p. 68: with constant expected returns,
`Δ_{t+1} rⁿ_{t+1} = −∑_{j ≥ 1} ωʲ Δ_{t+1} π_{t+1+j}`. -/
theorem bond_return_identity_const {om c : ℝ} {q rn r infl : ℕ → Ω → ℝ}
    (hb : BondReturn om q rn) (hr : ∀ t, r t = rn t - infl t) (hc : ConstExpReturn 𝔼 r c)
    (hq : 𝔼.Adapted q) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => om ^ (j + 1) * innov 𝔼 t (infl (t + 2 + j)) ω)
      (-innov 𝔼 t (rn (t + 1)) ω) :=
  (bond_return_identity_real 𝔼 hb hr (hq t) hT).congr
    (fun j => by simp [innov_future_return_zero 𝔼 hc]) rfl

/-- Cochrane (2023), eq. (3.23), p. 67: with constant expected returns and no growth,
`∑_{j ≥ 0} ωʲ Δ_{t+1} π_{t+1+j} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`. -/
theorem weighted_inflation_identity_const {ρ om c : ℝ} {v r rn infl s q : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t) (hb : BondReturn om q rn)
    (hc : ConstExpReturn 𝔼 r c) (hv : 𝔼.Adapted v) (hq : 𝔼.Adapted q) {t : ℕ} {ω : Ω}
    (hTv : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    (hTq : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0))
    {S : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S) :
    SeriesTo (fun j => om ^ j * innov 𝔼 t (infl (t + 1 + j)) ω) (-S) := by
  have h1 := inflation_identity_const 𝔼 h hr hc hv hTv hS
  have h2 := bond_return_identity_const 𝔼 hb hr hc hq hTq
  refine seriesTo_succ_iff.2 (h2.congr (fun j => ?_) ?_)
  · rw [show t + 2 + j = t + 1 + (j + 1) by omega]
  · simp only [pow_zero, one_mul, add_zero]
    linarith

/-- Cochrane (2023), p. 67 (one-period debt, time-varying expected returns): if `rⁿ_{t+1}` is
known at `t`, then `Δπ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`, i.e. the
discount-rate sum converges to `Δπ_{t+1} + S + G`. -/
theorem inflation_identity_one_period {ρ : ℝ} {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v) {t : ℕ}
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S G : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S)
    (hG : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) ω) G) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω)
      (innov 𝔼 t (infl (t + 1)) ω + S + G) := by
  refine (unexpected_inflation_identity 𝔼 h hr (hv t) hT hS hG).congr (fun _ => rfl) ?_
  rw [innov_of_known 𝔼 hrn, Pi.zero_apply, sub_zero]

/-- Cochrane (2023), p. 66 (constant expected returns, one-period debt, no growth):
`Δ_{t+1}π_{t+1} = −∑_{j ≥ 0} ρʲ Δ_{t+1} s̃_{t+1+j}`. -/
theorem inflation_identity_one_period_const {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hr : ∀ t, r t = rn t - infl t)
    (hc : ConstExpReturn 𝔼 r c) (hv : 𝔼.Adapted v) {t : ℕ}
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0))
    {S : ℝ} (hS : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) S) :
    innov 𝔼 t (infl (t + 1)) ω = -S := by
  have := inflation_identity_const 𝔼 h hr hc hv hT hS
  rw [innov_of_known 𝔼 hrn, Pi.zero_apply, sub_zero] at this
  exact this

end Cochrane.DebtDeficitsInflation.LinearizedIdentities
