/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.ForwardSolution

/-!
# Money in the government debt valuation equation

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.4, pp. 57–62.

Timing convention: `B t` and `M t` are the book's `B_{t−1}` and `M_{t−1}`, the nominal bonds and
non-interest-bearing money held from period `t − 1` into period `t`; `i t` is the book's `i_t`, the
rate on the bonds `B (t + 1)` sold at date `t`. `Λ` is a positive stochastic discount factor and
bonds are priced by `1/(1 + i_t) = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1})]` (p. 55).

## Main results

* `telescope`, `pv_iff_tvc`: for `Y_t = c_t + E_t Y_{t+1}` (signed `c`), the partial-sum identity
  and: given (absolute) summability, the present-value relation holds iff the terminal term
  `E_t Y_{t+T} → 0`.
* `E_next`: the nominal Euler equation `E_t[Λ_{t+1} D/P_{t+1}] = Λ_t D/((1+i_t)P_t)` for `D`
  known at `t` (needs the pull-out property).
* `pv_book_iff`: the general flow-to-valuation theorem in the book's form, both directions.
* (3.12) and its second form: `pv_3_12`, `pv_3_12b`; footnote 2 weight `weight_identity`.
* (3.10), (3.11): `pv_3_10`, `pv_3_11` (each: valuation ⇔ its own transversality condition).
* Survey error E13 ("these equivalent expressions", p. 57): `tvc_split`, `pv_3_10_iff_3_11`
  (equivalent under the money transversality condition), `pv_3_10_iff_money_tvc` (given (3.11),
  (3.10) holds iff the money transversality condition holds), and the counterexample
  `money_bubble` ((3.11) holds at every date, (3.10) at none).
* (3.13)–(3.15): `exPostReturn`, `flow_3_14`, `iterate_discount`, `pv_discount_iff`,
  `pv_3_15_finite`, `pv_3_15_iff`.
* (3.16), the zero bound, and survey error E14: `zero_bound_valuation` (from (3.10)),
  `full_interest_valuation` (`i = i^m`), `zero_bound_beta`, `zero_bound_E_outside`,
  `zero_bound_flow_total`, and `zero_bound_not_from_3_11` (the printed derivation "following
  (3.11)" fails without the money transversality condition).
* §3.4.2: `seigniorage_offset_term`, `seigniorage_offset_valuation`, `seigniorage_offset_flow`,
  `full_interest_split_irrelevant`, `passive_split`, and the arithmetic `seigniorage_2019`,
  `seigniorage_1980s`.
-/

namespace Cochrane.Generality.Money

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Telescoping and the transversality condition -/

/-- Cochrane (2023), footnote 1, p. 58 ("and iterate"): if `Y_t = c_t + E_t Y_{t+1}` with `Y`
adapted, then `Y_t = ∑_{j<T} E_t c_{t+j} + E_t Y_{t+T}`. -/
theorem telescope {Y c : ℕ → Ω → ℝ} (hYa : 𝔼.Adapted Y)
    (hY : ∀ t, Y t = c t + 𝔼.E t (Y (t + 1))) (t T : ℕ) :
    Y t = ∑ j ∈ Finset.range T, 𝔼.E t (c (t + j)) + 𝔼.E t (Y (t + T)) := by
  induction T with
  | zero => simp [hYa t]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    have h := congrArg (𝔼.E t) (hY (t + T))
    rw [map_add, 𝔼.tower (Nat.le_add_right t T)] at h
    rw [h, ← add_assoc t T 1]

/-- Cochrane (2023), p. 55 and footnote 1, p. 58: for `Y_t = c_t + E_t Y_{t+1}` and a summable
series `∑_j E_t c_{t+j}` (in `ℝ`, summable means absolutely summable; the `c` are signed), the
transversality condition `E_t Y_{t+T} → 0` holds iff `Y_t = ∑_j E_t c_{t+j}`. -/
theorem pv_iff_tvc {Y c : ℕ → Ω → ℝ} (hYa : 𝔼.Adapted Y)
    (hY : ∀ t, Y t = c t + 𝔼.E t (Y (t + 1))) (t : ℕ) (ω : Ω)
    (hs : Summable fun j => 𝔼.E t (c (t + j)) ω) :
    Tendsto (fun T => 𝔼.E t (Y (t + T)) ω) atTop (𝓝 0) ↔
      Y t ω = ∑' j, 𝔼.E t (c (t + j)) ω := by
  have he : ∀ T, 𝔼.E t (Y (t + T)) ω =
      Y t ω - ∑ j ∈ Finset.range T, 𝔼.E t (c (t + j)) ω := by
    intro T
    have h := congrFun (telescope 𝔼 hYa hY t T) ω
    simp only [Pi.add_apply, Finset.sum_apply] at h
    linarith
  have hlim : Tendsto (fun T => 𝔼.E t (Y (t + T)) ω) atTop
      (𝓝 (Y t ω - ∑' j, 𝔼.E t (c (t + j)) ω)) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h
    rwa [h, sub_self] at hlim

/-! ### The money economy -/

/-- Cochrane (2023), p. 55: bonds are priced by the stochastic discount factor,
`Q_t = 1/(1 + i_t) = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1})]`. -/
def BondEuler (Λ P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (fun ω => 1 / (1 + i t ω)) =
    𝔼.E t (fun ω => Λ (t + 1) ω / Λ t ω * (P t ω / P (t + 1) ω))

variable (Λ P i M B : ℕ → Ω → ℝ)

/-- Cochrane (2023), §3.3–3.4, pp. 55–59: the standing assumptions. `Λ > 0` is the stochastic
discount factor, `P > 0` the price level; the nominal discount factor `Λ_t/P_t` and `Λ_t⁻¹` are
known at `t`; bonds and money are known at `t` and predetermined (`B (t+1)`, `M (t+1)` are chosen
at `t`); `1 + i_t > 0`; bonds are priced by the stochastic discount factor (p. 55); and the
conditional expectations have the pull-out property. -/
structure Standing where
  pullOut : 𝔼.PullOut
  disc_pos : ∀ t ω, 0 < Λ t ω
  price_pos : ∀ t ω, 0 < P t ω
  nominal_adapted : 𝔼.Adapted (fun t ω => Λ t ω / P t ω)
  disc_inv_adapted : 𝔼.Adapted (fun t ω => (Λ t ω)⁻¹)
  bonds_adapted : 𝔼.Adapted B
  money_adapted : 𝔼.Adapted M
  bonds_pre : ∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)
  money_pre : ∀ t, 𝔼.E t (M (t + 1)) = M (t + 1)
  rate_gt : ∀ t ω, -1 < i t ω
  euler : BondEuler 𝔼 Λ P i

variable {Λ P i M B}

/-- Cochrane (2023), (3.9), p. 57: the flow condition with non-interest-bearing money,
`B_{t−1} + M_{t−1} = P_t s_t + B_t/(1 + i_t) + M_t`. -/
def Flow39 (P s i M B : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, B t ω + M t ω = P t ω * s t ω + B (t + 1) ω / (1 + i t ω) + M (t + 1) ω

/-- Cochrane (2023), p. 58: the flow condition when money pays interest `i^m` (discount basis),
`B_{t−1} + M_{t−1} = P_t s_t + B_t/(1 + i_t) + M_t/(1 + i^m_t)`. -/
def FlowIm (P s i im M B : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, B t ω + M t ω =
    P t ω * s t ω + B (t + 1) ω / (1 + i t ω) + M (t + 1) ω / (1 + im t ω)

/-- Cochrane (2023), pp. 57–58: (3.9) is the flow condition with `i^m = 0`. -/
theorem flow39_iff_flowIm (P s i M B : ℕ → Ω → ℝ) :
    Flow39 P s i M B ↔ FlowIm P s i (fun _ _ => 0) M B := by
  simp only [Flow39, FlowIm, add_zero, div_one]

/-- Cochrane (2023), (3.10)–(3.12), pp. 58–59: the present-value relation
`X_t/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t) d_{t+j}]` for the nominal liabilities `X`. -/
def PVRel (Λ P X d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Prop :=
  X t ω / P t ω = ∑' j, 𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω

/-- Cochrane (2023), p. 55: the transversality condition `lim_T E_t[Λ_{t+T} X_{t+T}/P_{t+T}] = 0`
(the book divides by the positive date-`t` constant `Λ_t`). -/
def TVC (Λ P X : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Prop :=
  Tendsto (fun T => 𝔼.E t (fun ω' => Λ (t + T) ω' * (X (t + T) ω' / P (t + T) ω')) ω) atTop
    (𝓝 0)

/-- Cochrane (2023), (3.10)–(3.12): summability of the present-value series. -/
def PVSummable (Λ d : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Prop :=
  Summable fun j => 𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω

/-- Cochrane (2023), (3.10), p. 58: the integrand `s_t + i_t M_t/((1 + i_t) P_t)` (book indices;
here `M (t + 1)` is the money held overnight from `t`). -/
noncomputable def term10 (P s i M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + i t ω / (1 + i t ω) * (M (t + 1) ω / P t ω)

/-- Cochrane (2023), (3.11), p. 58: the integrand `s_t + ΔM_t/P_t`. -/
noncomputable def term11 (P s M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + (M (t + 1) ω - M t ω) / P t ω

/-- Cochrane (2023), (3.12), p. 59: the integrand
`s_t + (i_t − i^m_t)/((1 + i_t)(1 + i^m_t)) · M_t/P_t`. -/
noncomputable def term12 (P s i im M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + (i t ω - im t ω) / ((1 + i t ω) * (1 + im t ω)) * (M (t + 1) ω / P t ω)

/-- Cochrane (2023), second display after (3.12), p. 59: the integrand
`s_t + (M_t/(1 + i^m_t) − M_{t−1})/P_t`. -/
noncomputable def term12b (P s im M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω + (M (t + 1) ω / (1 + im t ω) - M t ω) / P t ω

/-- Cochrane (2023), footnote 2, p. 59: `1/(1 + i^m) − 1/(1 + i) = (i − i^m)/((1 + i)(1 + i^m))`. -/
theorem weight_identity {x y : ℝ} (hx : 1 + x ≠ 0) (hy : 1 + y ≠ 0) :
    1 / (1 + y) - 1 / (1 + x) = (x - y) / ((1 + x) * (1 + y)) := by
  field_simp
  ring

/-- Cochrane (2023), p. 55 and footnote 1, p. 58: the nominal Euler equation: for `D` known at
`t`, `E_t[Λ_{t+1} D/P_{t+1}] = Λ_t D/((1 + i_t) P_t)`. -/
theorem E_next (hS : Standing 𝔼 Λ P i M B) (t : ℕ) {D : Ω → ℝ} (hD : 𝔼.E t D = D) :
    𝔼.E t (fun ω => Λ (t + 1) ω * (D ω / P (t + 1) ω)) =
      fun ω => Λ t ω * (D ω / (1 + i t ω) / P t ω) := by
  have hξ : 𝔼.E t (fun ω => Λ t ω / P t ω) = fun ω => Λ t ω / P t ω := hS.nominal_adapted t
  have hk : 𝔼.E t (D * fun ω => Λ t ω / P t ω) = D * fun ω => Λ t ω / P t ω := by
    rw [hS.pullOut t D _ hD, hξ]
  have he : (fun ω => Λ (t + 1) ω * (D ω / P (t + 1) ω)) =
      (D * fun ω => Λ t ω / P t ω) * fun ω => Λ (t + 1) ω / Λ t ω * (P t ω / P (t + 1) ω) := by
    funext ω
    have h1 := (hS.disc_pos t ω).ne'
    have h2 := (hS.price_pos t ω).ne'
    have h3 := (hS.price_pos (t + 1) ω).ne'
    simp only [Pi.mul_apply]
    field_simp
  rw [he, hS.pullOut t _ _ hk, ← hS.euler t]
  funext ω
  have h1 : 1 + i t ω ≠ 0 := by linarith [hS.rate_gt t ω]
  have h2 := (hS.price_pos t ω).ne'
  simp only [Pi.mul_apply]
  field_simp

/-- Cochrane (2023), p. 55: `E_t[(Λ_{t+j}/Λ_t) d] = Λ_t⁻¹ E_t[Λ_{t+j} d]` (pull-out of the known
`Λ_t⁻¹`). -/
theorem E_ratio (hS : Standing 𝔼 Λ P i M B) (t j : ℕ) (d : ℕ → Ω → ℝ) (ω : Ω) :
    𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω =
      (Λ t ω)⁻¹ * 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω := by
  have hk : 𝔼.E t (fun ω' => (Λ t ω')⁻¹) = fun ω' => (Λ t ω')⁻¹ := hS.disc_inv_adapted t
  have he : (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') =
      (fun ω' => (Λ t ω')⁻¹) * fun ω' => Λ (t + j) ω' * d (t + j) ω' := by
    funext ω'
    simp only [Pi.mul_apply]
    ring
  rw [he, hS.pullOut t _ _ hk]
  rfl

/-- Cochrane (2023), p. 55: the real value `Λ_t X_t/P_t` of liabilities `X` known at `t` is known
at `t`. -/
theorem adapted_val (hS : Standing 𝔼 Λ P i M B) {X : ℕ → Ω → ℝ} (hX : 𝔼.Adapted X) :
    𝔼.Adapted (fun t ω => Λ t ω * (X t ω / P t ω)) := by
  intro t
  have hξ : 𝔼.E t (fun ω => Λ t ω / P t ω) = fun ω => Λ t ω / P t ω := hS.nominal_adapted t
  have he : (fun ω => Λ t ω * (X t ω / P t ω)) = X t * fun ω => Λ t ω / P t ω := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  change 𝔼.E t (fun ω => Λ t ω * (X t ω / P t ω)) = fun ω => Λ t ω * (X t ω / P t ω)
  rw [he, hS.pullOut t _ _ (hX t), hξ]

/-- Cochrane (2023), pp. 55–59 (the general valuation theorem, both directions): if the real
value of the liabilities `X` obeys the flow recursion
`Λ_t X_t/P_t = Λ_t d_t + E_t[Λ_{t+1} X_{t+1}/P_{t+1}]` and the present-value series is summable,
then the transversality condition holds iff `X_t/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t) d_{t+j}]`. -/
theorem pv_book_iff (hS : Standing 𝔼 Λ P i M B) {X d : ℕ → Ω → ℝ} (hXa : 𝔼.Adapted X)
    (hrec : ∀ t, (fun ω => Λ t ω * (X t ω / P t ω)) = (fun ω => Λ t ω * d t ω) +
      𝔼.E t (fun ω => Λ (t + 1) ω * (X (t + 1) ω / P (t + 1) ω)))
    (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ d t ω) :
    TVC 𝔼 Λ P X t ω ↔ PVRel 𝔼 Λ P X d t ω := by
  have hrel : ∀ j, 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω =
      Λ t ω * 𝔼.E t (fun ω' => Λ (t + j) ω' / Λ t ω' * d (t + j) ω') ω := by
    intro j
    rw [E_ratio 𝔼 hS t j d ω]
    have := (hS.disc_pos t ω).ne'
    field_simp
  have hsum' : Summable fun j => 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω :=
    (hsum.mul_left (Λ t ω)).congr fun j => (hrel j).symm
  have key := pv_iff_tvc 𝔼 (Y := fun t ω => Λ t ω * (X t ω / P t ω))
    (c := fun t ω => Λ t ω * d t ω) (adapted_val 𝔼 hS hXa) hrec t ω hsum'
  unfold TVC PVRel
  refine key.trans ?_
  change Λ t ω * (X t ω / P t ω) =
      ∑' j, 𝔼.E t (fun ω' => Λ (t + j) ω' * d (t + j) ω') ω ↔ _
  rw [tsum_congr hrel, tsum_mul_left]
  exact mul_right_inj' (hS.disc_pos t ω).ne'

/-! ### Equations (3.10)–(3.12) -/

/-- Cochrane (2023), footnote 2, p. 59: the flow recursion behind (3.12). -/
theorem rec_3_12 (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) :
    (fun ω => Λ t ω * ((B + M) t ω / P t ω)) =
      (fun ω => Λ t ω * term12 P s i im M t ω) +
        𝔼.E t (fun ω => Λ (t + 1) ω * ((B + M) (t + 1) ω / P (t + 1) ω)) := by
  have hD : 𝔼.E t ((B + M) (t + 1)) = (B + M) (t + 1) := by
    simp only [Pi.add_apply, map_add, hS.bonds_pre, hS.money_pre]
  rw [E_next 𝔼 hS t hD]
  funext ω
  have h1 : 1 + i t ω ≠ 0 := by linarith [hS.rate_gt t ω]
  have h2 : 1 + im t ω ≠ 0 := by linarith [hm t ω]
  have h3 := (hS.price_pos t ω).ne'
  simp only [Pi.add_apply, term12]
  rw [hf t ω]
  field_simp
  ring

/-- Cochrane (2023), footnote 1 (second), p. 59: the flow recursion behind the second form of
(3.12). -/
theorem rec_3_12b (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) :
    (fun ω => Λ t ω * (B t ω / P t ω)) =
      (fun ω => Λ t ω * term12b P s im M t ω) +
        𝔼.E t (fun ω => Λ (t + 1) ω * (B (t + 1) ω / P (t + 1) ω)) := by
  rw [E_next 𝔼 hS t (hS.bonds_pre t)]
  funext ω
  have h1 : 1 + i t ω ≠ 0 := by linarith [hS.rate_gt t ω]
  have h2 : 1 + im t ω ≠ 0 := by linarith [hm t ω]
  have h3 := (hS.price_pos t ω).ne'
  have hb : B t ω = P t ω * s t ω + B (t + 1) ω / (1 + i t ω) +
      M (t + 1) ω / (1 + im t ω) - M t ω := by linarith [hf t ω]
  simp only [Pi.add_apply, term12b]
  rw [hb]
  field_simp
  ring

/-- Cochrane (2023), (3.12), p. 59: with interest on money, the flow condition and the
transversality condition on `B + M` are equivalent to
`(B_{t−1} + M_{t−1})/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + (i − i^m)/((1+i)(1+i^m)) M/P)]`. -/
theorem pv_3_12 (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ (term12 P s i im M) t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) (term12 P s i im M) t ω :=
  pv_book_iff 𝔼 hS (fun t => by simp only [Pi.add_apply, map_add, hS.bonds_adapted t,
    hS.money_adapted t]) (rec_3_12 𝔼 hS hm hf) t ω hsum

/-- Cochrane (2023), second display after (3.12), p. 59: with interest on money, the flow
condition and the transversality condition on `B` alone are equivalent to
`B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + (M_{t+j}/(1+i^m_{t+j}) − M_{t+j−1})/P_{t+j})]`. -/
theorem pv_3_12b (hS : Standing 𝔼 Λ P i M B) {s im : ℕ → Ω → ℝ} (hm : ∀ t ω, -1 < im t ω)
    (hf : FlowIm P s i im M B) (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ (term12b P s im M) t ω) :
    TVC 𝔼 Λ P B t ω ↔ PVRel 𝔼 Λ P B (term12b P s im M) t ω :=
  pv_book_iff 𝔼 hS hS.bonds_adapted (rec_3_12b 𝔼 hS hm hf) t ω hsum

/-- Cochrane (2023), (3.10) and (3.12), p. 59: with `i^m = 0` the integrand of (3.12) is that of
(3.10). -/
theorem term12_zero (P s i M : ℕ → Ω → ℝ) :
    term12 P s i (fun _ _ => 0) M = term10 P s i M := by
  funext t ω
  simp only [term12, term10, sub_zero, add_zero, mul_one]

/-- Cochrane (2023), (3.11) and (3.12), p. 59: with `i^m = 0` the second form of (3.12) is
(3.11). -/
theorem term12b_zero (P s M : ℕ → Ω → ℝ) :
    term12b P s (fun _ _ => 0) M = term11 P s M := by
  funext t ω
  simp only [term12b, term11, add_zero, div_one]

/-- Cochrane (2023), (3.10), p. 58 (with footnote 1): given the flow (3.9), the transversality
condition on `B + M` holds iff `(B_{t−1} + M_{t−1})/P_t =
∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + i_{t+j}M_{t+j}/((1+i_{t+j})P_{t+j}))]`. -/
theorem pv_3_10 (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (t : ℕ)
    (ω : Ω) (hsum : PVSummable 𝔼 Λ (term10 P s i M) t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) (term10 P s i M) t ω := by
  rw [← term12_zero] at hsum ⊢
  exact pv_3_12 𝔼 hS (fun _ _ => by norm_num) ((flow39_iff_flowIm P s i M B).mp hf) t ω hsum

/-- Cochrane (2023), (3.11), p. 58 (with footnote 1): given the flow (3.9), the transversality
condition on `B` alone holds iff
`B_{t−1}/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t)(s_{t+j} + ΔM_{t+j}/P_{t+j})]`. -/
theorem pv_3_11 (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (t : ℕ)
    (ω : Ω) (hsum : PVSummable 𝔼 Λ (term11 P s M) t ω) :
    TVC 𝔼 Λ P B t ω ↔ PVRel 𝔼 Λ P B (term11 P s M) t ω := by
  rw [← term12b_zero] at hsum ⊢
  exact pv_3_12b 𝔼 hS (fun _ _ => by norm_num) ((flow39_iff_flowIm P s i M B).mp hf) t ω hsum

/-! ### Survey error E13: (3.10) and (3.11) are equivalent only under the money TVC -/

/-- Cochrane (2023), p. 57 (E13): the terminal term of (3.10) is the terminal term of (3.11) plus
the money terminal term `E_t[Λ_{t+T} M_{t+T}/P_{t+T}]`. -/
theorem tvc_split (t T : ℕ) (ω : Ω) :
    𝔼.E t (fun ω' => Λ (t + T) ω' * ((B + M) (t + T) ω' / P (t + T) ω')) ω =
      𝔼.E t (fun ω' => Λ (t + T) ω' * (B (t + T) ω' / P (t + T) ω')) ω +
        𝔼.E t (fun ω' => Λ (t + T) ω' * (M (t + T) ω' / P (t + T) ω')) ω := by
  have he : (fun ω' => Λ (t + T) ω' * ((B + M) (t + T) ω' / P (t + T) ω')) =
      (fun ω' => Λ (t + T) ω' * (B (t + T) ω' / P (t + T) ω')) +
        fun ω' => Λ (t + T) ω' * (M (t + T) ω' / P (t + T) ω') := by
    funext ω'
    simp only [Pi.add_apply]
    ring
  rw [he, map_add, Pi.add_apply]

/-- Cochrane (2023), p. 57, "these equivalent expressions" (survey E13, corrected): under the
money transversality condition `E_t[Λ_{t+T} M_{t+T}/P_{t+T}] → 0`, (3.10) holds iff (3.11) holds. -/
theorem pv_3_10_iff_3_11 (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B)
    (t : ℕ) (ω : Ω) (h10 : PVSummable 𝔼 Λ (term10 P s i M) t ω)
    (h11 : PVSummable 𝔼 Λ (term11 P s M) t ω) (hM : TVC 𝔼 Λ P M t ω) :
    PVRel 𝔼 Λ P (B + M) (term10 P s i M) t ω ↔ PVRel 𝔼 Λ P B (term11 P s M) t ω := by
  rw [← pv_3_10 𝔼 hS hf t ω h10, ← pv_3_11 𝔼 hS hf t ω h11]
  unfold TVC at hM ⊢
  simp_rw [tvc_split 𝔼 t _ ω]
  constructor
  · intro h
    simpa using h.sub hM
  · intro h
    simpa using h.add hM

/-- Cochrane (2023), p. 57 (survey E13): if (3.11) holds, then (3.10) holds iff the money
transversality condition holds. -/
theorem pv_3_10_iff_money_tvc (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ}
    (hf : Flow39 P s i M B) (t : ℕ) (ω : Ω) (h10 : PVSummable 𝔼 Λ (term10 P s i M) t ω)
    (h11 : PVSummable 𝔼 Λ (term11 P s M) t ω) (h311 : PVRel 𝔼 Λ P B (term11 P s M) t ω) :
    PVRel 𝔼 Λ P (B + M) (term10 P s i M) t ω ↔ TVC 𝔼 Λ P M t ω := by
  rw [← pv_3_10 𝔼 hS hf t ω h10]
  have hB := (pv_3_11 𝔼 hS hf t ω h11).mpr h311
  unfold TVC at hB ⊢
  simp_rw [tvc_split 𝔼 t _ ω]
  constructor
  · intro h
    simpa using h.sub hB
  · intro h
    simpa using hB.add h

/-- Cochrane (2023), p. 57 (survey E13, counterexample): a perfect-foresight economy (a money
bubble: real money balances grow at the interest rate) satisfying the standing assumptions and
the flow (3.9), in which (3.11) holds at every date while (3.10) fails at every date, and the
money transversality condition fails. Here `Λ_t = βᵗ`, `P ≡ 1`, `1 + i = β⁻¹`, `B ≡ 0`,
`M_{t−1} = β⁻ᵗ`, `s_t = M_{t−1} − M_t`. -/
theorem money_bubble {β : ℝ} (hβ0 : 0 < β) :
    ∃ Λ P i M B s : ℕ → Unit → ℝ, Standing perfectForesight Λ P i M B ∧ Flow39 P s i M B ∧
      (∀ t, PVSummable perfectForesight Λ (term10 P s i M) t ()) ∧
      (∀ t, PVSummable perfectForesight Λ (term11 P s M) t ()) ∧
      (∀ t, PVRel perfectForesight Λ P B (term11 P s M) t ()) ∧
      (∀ t, ¬ PVRel perfectForesight Λ P (B + M) (term10 P s i M) t ()) ∧
      (∀ t, ¬ TVC perfectForesight Λ P M t ()) := by
  have hβ : β ≠ 0 := hβ0.ne'
  set Λ : ℕ → Unit → ℝ := fun t _ => β ^ t
  set P : ℕ → Unit → ℝ := fun _ _ => 1
  set i : ℕ → Unit → ℝ := fun _ _ => β⁻¹ - 1
  set M : ℕ → Unit → ℝ := fun t _ => β⁻¹ ^ t
  set B : ℕ → Unit → ℝ := fun _ _ => 0
  set s : ℕ → Unit → ℝ := fun t _ => β⁻¹ ^ t - β⁻¹ ^ (t + 1)
  have h10 : ∀ t ω, term10 P s i M t ω = 0 := by
    intro t ω
    simp only [term10, P, i, M, s, pow_succ]
    field_simp
    ring
  have h11 : ∀ t ω, term11 P s M t ω = 0 := by
    intro t ω
    simp only [term11, P, M, s]
    ring
  have hz10 : ∀ t, (fun j => perfectForesight.E t
      (fun ω' => Λ (t + j) ω' / Λ t ω' * term10 P s i M (t + j) ω') ()) = fun _ => 0 := by
    intro t
    funext j
    simp only [h10, mul_zero]
    rfl
  have hz11 : ∀ t, (fun j => perfectForesight.E t
      (fun ω' => Λ (t + j) ω' / Λ t ω' * term11 P s M (t + j) ω') ()) = fun _ => 0 := by
    intro t
    funext j
    simp only [h11, mul_zero]
    rfl
  refine ⟨Λ, P, i, M, B, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { pullOut := perfectForesight_pullOut
        disc_pos := fun t _ => pow_pos hβ0 t
        price_pos := fun _ _ => one_pos
        nominal_adapted := fun _ => rfl
        disc_inv_adapted := fun _ => rfl
        bonds_adapted := fun _ => rfl
        money_adapted := fun _ => rfl
        bonds_pre := fun _ => rfl
        money_pre := fun _ => rfl
        rate_gt := fun _ _ => by
          have : 0 < β⁻¹ := inv_pos.mpr hβ0
          simp only [i]
          linarith
        euler := fun t => by
          funext ω
          change 1 / (1 + (β⁻¹ - 1)) = β ^ (t + 1) / β ^ t * (1 / 1)
          rw [pow_succ]
          field_simp
          ring }
  · intro t ω
    simp only [P, B, s, M, pow_succ]
    ring
  · intro t
    unfold PVSummable
    rw [hz10 t]
    exact summable_zero
  · intro t
    unfold PVSummable
    rw [hz11 t]
    exact summable_zero
  · intro t
    unfold PVRel
    rw [hz11 t, tsum_zero]
    simp [B]
  · intro t
    unfold PVRel
    rw [hz10 t, tsum_zero]
    simp only [Pi.add_apply, B, M, P, zero_add, div_one]
    exact pow_ne_zero t (inv_ne_zero hβ)
  · intro t h
    unfold TVC at h
    have hc : (fun T => perfectForesight.E t
        (fun ω' => Λ (t + T) ω' * (M (t + T) ω' / P (t + T) ω')) ()) = fun _ => 1 := by
      funext T
      change β ^ (t + T) * (β⁻¹ ^ (t + T) / 1) = 1
      rw [div_one, ← mul_pow, mul_inv_cancel₀ hβ, one_pow]
    rw [hc] at h
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-! ### Ex-post returns, (3.13)–(3.15) -/

/-- Cochrane (2023), (3.13), p. 59: the ex-post real return from `t` to `t + 1` on the portfolio
of bonds and money, `R_{t+1} = (B_t + M_t)P_t/((Q_t B_t + M_t)P_{t+1})`, `Q_t = 1/(1 + i_t)`. -/
noncomputable def exPostReturn (P i M B : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (B (t + 1) ω + M (t + 1) ω) * P t ω /
    ((B (t + 1) ω / (1 + i t ω) + M (t + 1) ω) * P (t + 1) ω)

/-- Cochrane (2023), (3.14), p. 59: the flow (3.9) written with the ex-post return,
`(B_{t−1} + M_{t−1})/P_t = s_t + (Q_tB_t + M_t)/P_t = s_t + R_{t+1}⁻¹(B_t + M_t)/P_{t+1}`. -/
theorem flow_3_14 {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (t : ℕ) (ω : Ω)
    (hP0 : P t ω ≠ 0) (hP1 : P (t + 1) ω ≠ 0) (hBM : B (t + 1) ω + M (t + 1) ω ≠ 0) :
    (B t ω + M t ω) / P t ω = s t ω + (B (t + 1) ω / (1 + i t ω) + M (t + 1) ω) / P t ω ∧
      (B t ω + M t ω) / P t ω = s t ω + 1 / exPostReturn P i M B t ω *
        ((B (t + 1) ω + M (t + 1) ω) / P (t + 1) ω) := by
  have h1 : (B t ω + M t ω) / P t ω =
      s t ω + (B (t + 1) ω / (1 + i t ω) + M (t + 1) ω) / P t ω := by
    rw [hf t ω]
    field_simp
    ring
  refine ⟨h1, ?_⟩
  rw [h1, exPostReturn]
  field_simp

/-- Cochrane (2023), (3.15) and (3.6), pp. 56, 59: iterating `x_t = a_t + b_t x_{t+1}` gives
`x_t = ∑_{j<T} (∏_{k<j} b_{t+k}) a_{t+j} + (∏_{k<T} b_{t+k}) x_{t+T}` (pathwise, exact). -/
theorem iterate_discount {x a b : ℕ → ℝ} (h : ∀ t, x t = a t + b t * x (t + 1)) (t T : ℕ) :
    x t = ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j) +
      (∏ k ∈ Finset.range T, b (t + k)) * x (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, Finset.prod_range_succ, h (t + T), ← add_assoc t T 1]
    ring

/-- Cochrane (2023), (3.15), p. 59: if the discounted series is summable, the pathwise
present-value relation `x_t = ∑_j (∏_{k<j} b_{t+k}) a_{t+j}` holds iff the discounted terminal
value `(∏_{k<T} b_{t+k}) x_{t+T}` tends to zero. -/
theorem pv_discount_iff {x a b : ℕ → ℝ} (h : ∀ t, x t = a t + b t * x (t + 1)) (t : ℕ)
    (hs : Summable fun j => (∏ k ∈ Finset.range j, b (t + k)) * a (t + j)) :
    Tendsto (fun T => (∏ k ∈ Finset.range T, b (t + k)) * x (t + T)) atTop (𝓝 0) ↔
      x t = ∑' j, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j) := by
  have he : ∀ T, (∏ k ∈ Finset.range T, b (t + k)) * x (t + T) =
      x t - ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j) := by
    intro T
    have := iterate_discount h t T
    linarith
  have hlim : Tendsto (fun T => (∏ k ∈ Finset.range T, b (t + k)) * x (t + T)) atTop
      (𝓝 (x t - ∑' j, (∏ k ∈ Finset.range j, b (t + k)) * a (t + j))) := by
    simp_rw [he]
    exact tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
  constructor
  · intro h0
    have := tendsto_nhds_unique hlim h0
    linarith
  · intro h1
    rwa [h1, sub_self] at hlim

/-- Cochrane (2023), (3.15), p. 59, finite horizon: along every path,
`(B_{t−1} + M_{t−1})/P_t = ∑_{j<T} (∏_{k=1}^{j} R_{t+k}⁻¹) s_{t+j}
  + (∏_{k=1}^{T} R_{t+k}⁻¹)(B_{t+T−1} + M_{t+T−1})/P_{t+T}`. -/
theorem pv_3_15_finite {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (ω : Ω)
    (hP : ∀ t, P t ω ≠ 0) (hBM : ∀ t, B (t + 1) ω + M (t + 1) ω ≠ 0) (t T : ℕ) :
    (B t ω + M t ω) / P t ω =
      ∑ j ∈ Finset.range T, (∏ k ∈ Finset.range j, 1 / exPostReturn P i M B (t + k) ω) *
        s (t + j) ω +
      (∏ k ∈ Finset.range T, 1 / exPostReturn P i M B (t + k) ω) *
        ((B (t + T) ω + M (t + T) ω) / P (t + T) ω) :=
  iterate_discount (x := fun t => (B t ω + M t ω) / P t ω) (a := fun t => s t ω)
    (fun t => (flow_3_14 hf t ω (hP t) (hP (t + 1)) (hBM t)).2) t T

/-- Cochrane (2023), (3.15), p. 59: along every path, the ex-post-return present value
`(B_{t−1} + M_{t−1})/P_t = ∑_j (∏_{k=1}^{j} R_{t+k}⁻¹) s_{t+j}` holds iff the ex-post discounted
terminal value tends to zero (given summability). -/
theorem pv_3_15_iff {s : ℕ → Ω → ℝ} (hf : Flow39 P s i M B) (ω : Ω)
    (hP : ∀ t, P t ω ≠ 0) (hBM : ∀ t, B (t + 1) ω + M (t + 1) ω ≠ 0) (t : ℕ)
    (hs : Summable fun j => (∏ k ∈ Finset.range j, 1 / exPostReturn P i M B (t + k) ω) *
      s (t + j) ω) :
    Tendsto (fun T => (∏ k ∈ Finset.range T, 1 / exPostReturn P i M B (t + k) ω) *
        ((B (t + T) ω + M (t + T) ω) / P (t + T) ω)) atTop (𝓝 0) ↔
      (B t ω + M t ω) / P t ω =
        ∑' j, (∏ k ∈ Finset.range j, 1 / exPostReturn P i M B (t + k) ω) * s (t + j) ω :=
  pv_discount_iff (x := fun t => (B t ω + M t ω) / P t ω) (a := fun t => s t ω)
    (fun t => (flow_3_14 hf t ω (hP t) (hP (t + 1)) (hBM t)).2) t hs

/-! ### The zero bound, (3.16), and survey error E14 -/

/-- Cochrane (2023), §3.4.1, p. 59: at the zero bound `i = 0` money and bonds are perfect
substitutes: the flow (3.9) involves only `B + M`. -/
theorem zero_bound_flow_total {s : ℕ → Ω → ℝ} (hi : ∀ t ω, i t ω = 0) :
    Flow39 P s i M B ↔
      ∀ t ω, (B + M) t ω = P t ω * s t ω + (B + M) (t + 1) ω := by
  simp only [Flow39, Pi.add_apply, hi, add_zero, div_one]
  constructor <;> intro h t ω <;> linarith [h t ω]

/-- Cochrane (2023), (3.16), p. 59, derived (correctly) from (3.10) (survey E14): at the zero
bound `i = 0` the integrand of (3.10) is the surplus, so the valuation reads
`(B_{t−1} + M_{t−1})/P_t = ∑_j E_t[(Λ_{t+j}/Λ_t) s_{t+j}]`, equivalent to the transversality
condition on `B + M`. -/
theorem zero_bound_valuation (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ}
    (hf : Flow39 P s i M B) (hi : ∀ t ω, i t ω = 0) (t : ℕ) (ω : Ω)
    (hsum : PVSummable 𝔼 Λ s t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) s t ω := by
  have he : term10 P s i M = s := by
    funext t ω
    simp only [term10, hi, zero_div, zero_mul, add_zero]
  rw [← he] at hsum ⊢
  exact pv_3_10 𝔼 hS hf t ω hsum

/-- Cochrane (2023), p. 60: with full interest on money, `i^m = i`, the integrand of (3.12) is the
surplus, and (3.16) holds as at the zero bound. -/
theorem full_interest_valuation (hS : Standing 𝔼 Λ P i M B) {s : ℕ → Ω → ℝ}
    (hf : FlowIm P s i i M B) (t : ℕ) (ω : Ω) (hsum : PVSummable 𝔼 Λ s t ω) :
    TVC 𝔼 Λ P (B + M) t ω ↔ PVRel 𝔼 Λ P (B + M) s t ω := by
  have he : term12 P s i i M = s := by
    funext t ω
    simp only [term12, sub_self, zero_div, zero_mul, add_zero]
  rw [← he] at hsum ⊢
  exact pv_3_12 𝔼 hS hS.rate_gt hf t ω hsum

/-- Cochrane (2023), (3.16), p. 59, with the book's discounting `Λ_{t+j}/Λ_t = βʲ` (deterministic
`Λ_t = βᵗ`): the right-hand side is `∑_j βʲ E_t s_{t+j}`. -/
theorem zero_bound_beta {β : ℝ} (hβ : β ≠ 0) (hΛ : ∀ t ω, Λ t ω = β ^ t) (X s : ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) :
    PVRel 𝔼 Λ P X s t ω ↔ X t ω / P t ω = ∑' j, β ^ j * 𝔼.E t (s (t + j)) ω := by
  unfold PVRel
  have he : ∀ j, (fun ω' => Λ (t + j) ω' / Λ t ω' * s (t + j) ω') = β ^ j • s (t + j) := by
    intro j
    funext ω'
    simp only [hΛ, Pi.smul_apply, smul_eq_mul, pow_add]
    field_simp
  simp_rw [he, map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), (3.16), p. 59, with the expectation outside the sum as printed: for bounded
surpluses and `0 ≤ β < 1`, `∑_j βʲ E_t s_{t+j} = E_t ∑_j βʲ s_{t+j}`. -/
theorem zero_bound_E_outside {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ K) (t : ℕ) (ω : Ω) :
    ∑' j, β ^ j * 𝔼.E t (s (t + j)) ω = 𝔼.E t (fun ω' => ∑' j, β ^ j * s (t + j) ω') ω := by
  have hb : ∀ k ω', |(β ^ k • s (t + k)) ω'| ≤ β ^ k * K := by
    intro k ω'
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hs (t + k) ω') (pow_nonneg hβ0 k)
  have h := 𝔼.E_tsum hβ0 hβ1 hb t ω
  simp only [Pi.smul_apply, smul_eq_mul, map_smul] at h
  rw [h]

/-- Cochrane (2023), p. 59, "Following (3.11), we still have (3.16)" (survey E14, counterexample):
a perfect-foresight economy at the zero bound (Friedman-rule deflation `P_t = βᵗ`, `Λ_t = βᵗ`,
constant money `m ≠ 0`, no bonds, no surpluses) that satisfies the standing assumptions, the flow
(3.9) and (3.11) at every date, but violates (3.16) at every date. (3.16) follows from (3.10), not
from (3.11); the two differ by the money transversality condition. -/
theorem zero_bound_not_from_3_11 {β m : ℝ} (hβ0 : 0 < β) (hm : m ≠ 0) :
    ∃ Λ P i M B s : ℕ → Unit → ℝ, Standing perfectForesight Λ P i M B ∧ Flow39 P s i M B ∧
      (∀ t ω, i t ω = 0) ∧ (∀ t, PVRel perfectForesight Λ P B (term11 P s M) t ()) ∧
      (∀ t, ¬ PVRel perfectForesight Λ P (B + M) s t ()) := by
  have hβ : β ≠ 0 := hβ0.ne'
  set Λ : ℕ → Unit → ℝ := fun t _ => β ^ t
  set P : ℕ → Unit → ℝ := fun t _ => β ^ t
  set M : ℕ → Unit → ℝ := fun _ _ => m
  set z : ℕ → Unit → ℝ := fun _ _ => 0
  have hz : ∀ t, (fun j => perfectForesight.E t
      (fun ω' => Λ (t + j) ω' / Λ t ω' * z (t + j) ω') ()) = fun _ => 0 := by
    intro t
    funext j
    simp only [z, mul_zero]
    rfl
  have h11 : term11 P z M = z := by
    funext t ω
    simp only [term11, z, M, sub_self, zero_div, add_zero]
  refine ⟨Λ, P, z, M, z, z, ?_, ?_, fun _ _ => rfl, ?_, ?_⟩
  · exact
      { pullOut := perfectForesight_pullOut
        disc_pos := fun t _ => pow_pos hβ0 t
        price_pos := fun t _ => pow_pos hβ0 t
        nominal_adapted := fun _ => rfl
        disc_inv_adapted := fun _ => rfl
        bonds_adapted := fun _ => rfl
        money_adapted := fun _ => rfl
        bonds_pre := fun _ => rfl
        money_pre := fun _ => rfl
        rate_gt := fun _ _ => by simp only [z]; norm_num
        euler := fun t => by
          funext ω
          change 1 / (1 + 0) = β ^ (t + 1) / β ^ t * (β ^ t / β ^ (t + 1))
          rw [add_zero]
          have h1 : β ^ t ≠ 0 := pow_ne_zero t hβ
          have h2 : β ^ (t + 1) ≠ 0 := pow_ne_zero (t + 1) hβ
          field_simp }
  · intro t ω
    simp only [z, M]
    ring
  · intro t
    unfold PVRel
    rw [h11, hz t, tsum_zero]
    simp [z]
  · intro t
    unfold PVRel
    rw [hz t, tsum_zero]
    simp only [Pi.add_apply, z, M, P, zero_add]
    exact div_ne_zero hm (pow_ne_zero t hβ)

/-! ### Seigniorage, §3.4.2 -/

/-- Cochrane (2023), p. 60: the surplus net of seigniorage counted as an interest saving,
`s_t − i_tM_t/((1 + i_t)P_t)` ("the rest of the government spends seigniorage"). -/
noncomputable def offsetSurplus (P s i M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => s t ω - i t ω / (1 + i t ω) * (M (t + 1) ω / P t ω)

/-- Cochrane (2023), p. 60: if the rest of the government spends seigniorage, the integrand of
(3.10) is the surplus `s` exclusive of seigniorage. -/
theorem seigniorage_offset_term (P s i M : ℕ → Ω → ℝ) :
    term10 P (offsetSurplus P s i M) i M = s := by
  funext t ω
  simp only [term10, offsetSurplus]
  ring

/-- Cochrane (2023), p. 60, "any seigniorage effect of monetary policy vanishes": with offsetting
surpluses, (3.10) is the money-free valuation `(B + M)/P = ∑_j E_t[(Λ_{t+j}/Λ_t) s_{t+j}]`,
whatever the path of money. -/
theorem seigniorage_offset_valuation (P s i M B : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    PVRel 𝔼 Λ P (B + M) (term10 P (offsetSurplus P s i M) i M) t ω ↔
      PVRel 𝔼 Λ P (B + M) s t ω := by
  rw [seigniorage_offset_term]

/-- Cochrane (2023), p. 60: with offsetting surpluses the flow condition involves only total debt,
`B_{t−1} + M_{t−1} = P_t s_t + (B_t + M_t)/(1 + i_t)`. -/
theorem seigniorage_offset_flow (P s i M B : ℕ → Ω → ℝ) (hP : ∀ t ω, P t ω ≠ 0)
    (hi : ∀ t ω, 1 + i t ω ≠ 0) :
    Flow39 P (offsetSurplus P s i M) i M B ↔
      ∀ t ω, (B + M) t ω = P t ω * s t ω + (B + M) (t + 1) ω / (1 + i t ω) := by
  have key : ∀ t ω, P t ω * offsetSurplus P s i M t ω + B (t + 1) ω / (1 + i t ω) +
      M (t + 1) ω = P t ω * s t ω + (B + M) (t + 1) ω / (1 + i t ω) := by
    intro t ω
    have h1 := hP t ω
    have h2 := hi t ω
    simp only [offsetSurplus, Pi.add_apply]
    field_simp
    ring
  simp only [Flow39, Pi.add_apply]
  constructor
  · intro h t ω
    rw [h t ω, key t ω]
    simp only [Pi.add_apply]
  · intro h t ω
    rw [h t ω, key t ω]
    simp only [Pi.add_apply]

/-- Cochrane (2023), pp. 60–62: with full interest on money (`i^m = i`) only total debt matters:
two splits of the same total `B + M` satisfy the flow condition together, and the valuation
integrand is the surplus, so the central bank can passively supply any money demanded. -/
theorem full_interest_split_irrelevant (P s i : ℕ → Ω → ℝ) {M₁ B₁ M₂ B₂ : ℕ → Ω → ℝ}
    (htot : B₁ + M₁ = B₂ + M₂) :
    (FlowIm P s i i M₁ B₁ ↔ FlowIm P s i i M₂ B₂) ∧ term12 P s i i M₁ = s ∧
      term12 P s i i M₂ = s := by
  have key : ∀ (M B : ℕ → Ω → ℝ), FlowIm P s i i M B ↔
      ∀ t ω, (B + M) t ω = P t ω * s t ω + ((B + M) (t + 1) ω) / (1 + i t ω) := by
    intro M B
    simp only [FlowIm, Pi.add_apply, add_div, add_assoc]
  refine ⟨by rw [key, key, htot], ?_, ?_⟩ <;>
  · funext t ω
    simp only [term12, sub_self, zero_div, zero_mul, add_zero]

/-- Cochrane (2023), p. 61: a passive money supply. Given total nominal debt `D` and money demand
`MV = Py` (`V ≠ 0`), the split `M = Py/V`, `B = D − M` meets money demand and leaves total debt
unchanged. -/
theorem passive_split (D P y : ℕ → Ω → ℝ) {V : ℝ} (hV : V ≠ 0) :
    (∀ t ω, (fun t ω => P t ω * y t ω / V) t ω * V = P t ω * y t ω) ∧
      ((fun t ω => D t ω - P t ω * y t ω / V) + fun t ω => P t ω * y t ω / V) = D := by
  refine ⟨fun t ω => by field_simp, ?_⟩
  funext t ω
  simp only [Pi.add_apply]
  ring

/-- Cochrane (2023), p. 60, U.S. 2019 (dollar amounts in billions): seigniorage counted as interest
savings `2% × 1500 = 30`, which is `3%` of a `1000` deficit, under `1%` of `5000` spending and
`0.15%` of a `20000` GDP; `5% × 1500 = 75`; a one-point rate rise gives `1% × 1500 = 15`. -/
theorem seigniorage_2019 :
    (2 / 100 : ℝ) * 1500 = 30 ∧ (30 : ℝ) / 1000 = 3 / 100 ∧ (30 : ℝ) / 5000 < 1 / 100 ∧
      (30 : ℝ) / 20000 = 15 / 10000 ∧ (5 / 100 : ℝ) * 1500 = 75 ∧ (1 / 100 : ℝ) * 1500 = 15 := by
  norm_num

/-- Cochrane (2023), pp. 60–61, U.S. early 1980s (billions): currency `100` over GDP `3000` is
`3.3%`; `10% × 100 = 10` of seigniorage is `0.33%` of GDP and less than a tenth of a `200`
deficit; debt `1000` is a third of GDP. The stated "$200 billion or 5% of GDP" is inconsistent
with the stated GDP: `200/3000 = 6.7%`. -/
theorem seigniorage_1980s :
    (100 : ℝ) / 3000 = 1 / 30 ∧ (10 / 100 : ℝ) * 100 = 10 ∧ (10 : ℝ) / 3000 = 1 / 300 ∧
      (10 : ℝ) / 200 < 1 / 10 ∧ (1000 : ℝ) / 3000 = 1 / 3 ∧ (200 : ℝ) / 3000 = 1 / 15 ∧
      (5 / 100 : ℝ) < 1 / 15 := by
  norm_num

end Cochrane.Generality.Money
