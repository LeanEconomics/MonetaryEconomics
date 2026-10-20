/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilAssumptions

/-!
# How many lags of `q` the multiplier rule needs ((1.24), p. 554)

Woodford (2003), *Interest and Prices*, Chapter 8, eq. (1.24), p. 554, with (1.17), p. 551, and
Assumption 8.5 (App. G.2, p. 719).

The state (1.24) is `Z̄_t = (Z_t, q_{t−1}, …, q_{t−d}, v_{t−1}, …, v_{t−k})` with `k = rank Λ` and
`d = min(k, n_z − 1)`. The question is whether `d` lags of `q` (with `k` lags of `v`) suffice to
recover the multipliers `M_{t−1}` time-invariantly (the rule (1.17)). They do, for `k ≥ 1`:

* `k < n_z` (so `d = k`): the rule of `Prop82General.KrylovBound.gRule` with window `k` uses
  exactly `k` lags of `q` and of `v` (second part of Assumption 8.5); `rule_lags_lt`.
* `k = n_z` (so `d = k − 1`): the **first** part of Assumption 8.5 (`B₂', B₂'Λ, …, B₂'Λ^{k−1}`
  independent, hence a basis) recovers `M_{t−k}` from `v_{t−k}, …, v_{t−1}` and
  `q_{t−k+1}, …, q_{t−1}`, and then `M_{t−1}`: `gRule1`, `multiplier_rule1`, `rule_lags_full`.
  This is what the first part of Assumption 8.5 is for.
* `k = 0`: `Λ = 0` and `Ẽ = 0` (`rank Λ = rank Ẽ`), so `M_{t−1} = q_{t−1}` needs one lag of `q`
  although `d = 0` (`rule_lags_zero`); but then the constraint (1.27) `Ẽ z_{t₀} = ē` is vacuous and
  the initial multipliers do not affect optimality, so nothing is lost.
-/

namespace Woodford.OptimalPolicyRules.MultiplierLags

open Matrix GeneralSetup PencilSplit Prop81General Prop82General.KrylovBound
  Prop82General.Prop82M TargetCriterion.Recursion TargetCriterion.Prop81 TargetCriterion.Prop82
  GeneralFOC.LQ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), Assumption 8.5 (first part), App. G.2: the observation map
`m ↦ (B₂' m, B₂'Λ m, …, B₂'Λ^{k−1} m)`. -/
def obsMap (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ) (k : ℕ) : (ι → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  (Matrix.of fun (j : Fin k) i => (B2 ᵥ* Λ ^ (j : ℕ)) i).mulVecLin

/-- Woodford (2003), Assumption 8.5 (first part) with `k = n_z`: the `k` vectors `B₂'Λʲ`,
`j < k`, form a basis, so the observation map is injective. -/
theorem obsMap_injective {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} {k : ℕ}
    (h : LinearIndependent ℝ (fun j : Fin k => B2 ᵥ* Λ ^ (j : ℕ))) (hk : k = Fintype.card ι) :
    Function.Injective (obsMap Λ B2 k) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro m hm
  rw [LinearMap.mem_ker] at hm
  rw [Submodule.mem_bot]
  rcases isEmpty_or_nonempty (Fin k) with hke | hkn
  · have : IsEmpty ι := by
      rw [← Fintype.card_eq_zero_iff, ← hk]
      simpa using hke
    funext i
    exact isEmptyElim i
  have htop := h.span_eq_top_of_card_eq_finrank (by simp [hk])
  have hmem : m ∈ Submodule.span ℝ (Set.range fun j : Fin k => B2 ᵥ* Λ ^ (j : ℕ)) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hdot : ∀ j : Fin k, (B2 ᵥ* Λ ^ (j : ℕ)) ⬝ᵥ m = 0 := fun j => by
    have := congrFun hm j
    simpa [obsMap, mulVec, dotProduct] using this
  have hmm : m ⬝ᵥ m = 0 := by
    calc m ⬝ᵥ m = (∑ j, c j • (B2 ᵥ* Λ ^ (j : ℕ))) ⬝ᵥ m := by rw [hc]
      _ = 0 := by
        rw [sum_dotProduct]
        exact Finset.sum_eq_zero fun j _ => by rw [smul_dotProduct, hdot j, smul_zero]
  exact dotProduct_self_eq_zero.mp hmm

/-- Woodford (2003), Assumption 8.5 (first part), `k = n_z`: the inverse of the observation map. -/
noncomputable def obsEquiv {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} {k : ℕ}
    (h : LinearIndependent ℝ (fun j : Fin k => B2 ᵥ* Λ ^ (j : ℕ))) (hk : k = Fintype.card ι) :
    (ι → ℝ) ≃ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.linearEquivOfInjective (obsMap Λ B2 k) (obsMap_injective h hk) (by simp [hk])

/-- Woodford (2003), (1.17) with (1.24) for `k = n_z`: the rule using `v_{s₀}, …, v_{s₀+k−1}`
(`vs j = v_{s₀+j}`) and only `q_{s₀+1}, …, q_{s₀+k−1}` (`qs i = q_{s₀+1+i}`, `k − 1 = d` lags). -/
noncomputable def gRule1 (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ) {k : ℕ}
    (E : (ι → ℝ) ≃ₗ[ℝ] (Fin k → ℝ)) (qs : ℕ → ι → ℝ) (vs : ℕ → ℝ) : ι → ℝ :=
  Λ ^ (k - 1) *ᵥ E.symm (fun j => -vs j -
      ∑ i ∈ Finset.range (j : ℕ), B2 ⬝ᵥ (Λ ^ ((j : ℕ) - 1 - i) *ᵥ qs i)) +
    ∑ i ∈ Finset.range (k - 1), Λ ^ (k - 1 - 1 - i) *ᵥ qs i

/-- Woodford (2003), (1.17), (1.24) and Assumption 8.5 (first part), `k = n_z ≥ 1`: if (1.20)
holds on `s₀ + 1, …, s₀ + k − 1` and (1.19) on `s₀, …, s₀ + k − 1`, the multiplier `M_{s₀+k−1}` is
`gRule1` of `v_{s₀..s₀+k−1}` and `q_{s₀+1..s₀+k−1}`. -/
theorem multiplier_rule1 {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} {k : ℕ}
    (h : LinearIndependent ℝ (fun j : Fin k => B2 ᵥ* Λ ^ (j : ℕ))) (hk : k = Fintype.card ι)
    (hk1 : 1 ≤ k) {s0 : ℕ} {m q : ℕ → ι → ℝ} {v : ℕ → ℝ}
    (h120 : ∀ j, 1 ≤ j → j ≤ k - 1 → m (s0 + j) = Λ *ᵥ m (s0 + j - 1) + q (s0 + j))
    (h119 : ∀ j, j ≤ k - 1 → B2 ⬝ᵥ m (s0 + j) + v (s0 + j) = 0) :
    m (s0 + (k - 1)) =
      gRule1 Λ B2 (obsEquiv h hk) (fun i => q (s0 + 1 + i)) (fun j => v (s0 + j)) := by
  have hobs : obsEquiv h hk (m s0) = fun j : Fin k => -v (s0 + (j : ℕ)) -
      ∑ i ∈ Finset.range (j : ℕ), B2 ⬝ᵥ (Λ ^ ((j : ℕ) - 1 - i) *ᵥ q (s0 + 1 + i)) := by
    funext j
    have hit := iterate_rec (Λ := Λ) (m := m) (q := q) (t := s0) (n := (j : ℕ))
      (fun i hi1 hi2 => h120 i hi1 (by have := j.isLt; omega))
    have h19 := h119 (j : ℕ) (by have := j.isLt; omega)
    rw [hit, dotProduct_add, dotProduct_sum] at h19
    change (obsMap Λ B2 k) (m s0) j = _
    simp only [obsMap, mulVecLin_apply]
    change (B2 ᵥ* Λ ^ (j : ℕ)) ⬝ᵥ m s0 = _
    rw [← dotProduct_mulVec]
    linarith
  have hm0 : m s0 = (obsEquiv h hk).symm (fun j : Fin k => -v (s0 + (j : ℕ)) -
      ∑ i ∈ Finset.range (j : ℕ), B2 ⬝ᵥ (Λ ^ ((j : ℕ) - 1 - i) *ᵥ q (s0 + 1 + i))) := by
    rw [← hobs, LinearEquiv.symm_apply_apply]
  rw [iterate_rec (fun i hi1 hi2 => h120 i hi1 hi2), gRule1, ← hm0]

/-- Woodford (2003), (1.17), (1.24), Proposition 8.2 and Assumption 8.5, **`k = n_z`**: along a
solution of (1.1) + (1.9) with the recovered initial multipliers, one fixed rule gives
`M_{t−1} = gRule1(q_{t−1}, …, q_{t−k+1}; v_{t−1}, …, v_{t−k})` at every `t ≥ t₀` — `d = k − 1`
lags of `q` suffice. -/
theorem rule_lags_full {Ω ιZ ιτ : Type*} [Fintype ιZ] [DecidableEq ιZ] [Fintype ιτ]
    {P : LQProblem ιZ ι ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0)
    (h85a : LinearIndependent ℝ (fun j : Fin H.Λ.rank => P.sys.B2 ᵥ* H.Λ ^ (j : ℕ)))
    (hfull : H.Λ.rank = Fintype.card ι) (hk1 : 1 ≤ H.Λ.rank) {D : ℕ} (hD : D + 1 ≤ t0)
    (hDk : H.Λ.rank ≤ D) {Mh qh : ℕ → Ω → ι → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) {c : ℕ → Ω → ι → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ι) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ι → ℝ}
    (hs : FOCSystem P 𝔼 c t0 Z0 (Mh (t0 - 1)) y φ) :
    ∀ t, t0 ≤ t → ∀ ω, Mpart (φ t ω) =
      gRule1 H.Λ P.sys.B2 (obsEquiv h85a hfull)
        (fun i => splice t0 qh (H.Qop (xproc P y)) (t - H.Λ.rank + 1 + i) ω)
        (fun j => splice t0 vh (vproc P y) (t - H.Λ.rank + j) ω) := by
  obtain ⟨h120, h119⟩ := histThen_rec H hD hhist hs
  intro t ht ω
  set k := H.Λ.rank with hkdef
  have hrule := multiplier_rule1 h85a hfull hk1 (s0 := t - k)
    (m := fun s => histThen t0 Mh φ s ω) (q := fun s => splice t0 qh (H.Qop (xproc P y)) s ω)
    (v := fun s => splice t0 vh (vproc P y) s ω)
    (fun j hj1 hjK => h120 (t - k + j) (by omega) ω)
    (fun j hjK => h119 (t - k + j) (by omega) ω)
  rw [show t - k + (k - 1) = t - 1 by omega] at hrule
  rw [← hrule]
  by_cases hlt : t - 1 < t0
  · have ht0 : t = t0 := by omega
    subst ht0
    simp only [histThen, hlt, ↓reduceIte]
    exact hs.2.2.2.1 ω
  · simp only [histThen, hlt, ↓reduceIte, show t - 1 + 1 = t by omega]

/-- Woodford (2003), (1.17), (1.24), **`1 ≤ k < n_z`** (`d = k`): the rule `gRule` with window
`k` uses `k = d` lags of `q` and of `v` (`Prop82General.Prop82M.prop82M_multiplier_rule` with
`D = k`). -/
theorem rule_lags_lt {Ω ιZ ιτ : Type*} [Fintype ιZ] [DecidableEq ιZ] [Fintype ιτ]
    {P : LQProblem ιZ ι ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (h85 : TargetCriterion.Krylov.Assumption85b H.Λ P.sys.B2)
    (hk1 : 1 ≤ H.Λ.rank) (hD : H.Λ.rank + 1 ≤ t0) {Mh qh : ℕ → Ω → ι → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 H.Λ.rank Mh qh vh) {c : ℕ → Ω → ι → ℝ}
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ι) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ι → ℝ}
    (hs : FOCSystem P 𝔼 c t0 Z0 (Mh (t0 - 1)) y φ) :
    ∃ C : Matrix ι (Fin H.Λ.rank) ℝ, ∀ t, t0 ≤ t → ∀ ω,
      Mpart (φ t ω) = gRule H.Λ P.sys.B2 C H.Λ.rank
        (fun i => splice t0 qh (H.Qop (xproc P y)) (t - H.Λ.rank + i) ω)
        (fun i => splice t0 vh (vproc P y) (t - H.Λ.rank + i) ω) :=
  prop82M_multiplier_rule H h85 hD hk1 le_rfl hhist hs

omit [DecidableEq ι] in
/-- Woodford (2003), (1.24) (tool): a real matrix of rank zero is zero. -/
theorem eq_zero_of_rank_zero {m : Type*} {M : Matrix m ι ℝ} (h : M.rank = 0) : M = 0 := by
  have hr : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h
  ext i j
  classical
  have : M *ᵥ Pi.single j 1 ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
  rw [hr, Submodule.mem_bot] at this
  have := congrFun this i
  simpa [mulVec_single_one] using this

/-- Woodford (2003), (1.24) with `k = 0`: then `Λ = 0`, so (1.20) is `M_t = q_t` and the rule is
`M_{t−1} = q_{t−1}` — one lag of `q` although `d = 0`; and `Ẽ = 0` (`rank Λ = rank Ẽ`), so the
initial constraint (1.27) is vacuous. -/
theorem rule_lags_zero {Ω ιZ : Type*} [Fintype ιZ] [DecidableEq ιZ] {S : LinearRESystem ιZ ι}
    {β : ℝ} (hβ : β ≠ 0) {J : Matrix (ιZ ⊕ ι) ιZ ℝ} (hK : (Kmat S J).det ≠ 0)
    (hk : (Λmat S β J).rank = 0) {M q : ℕ → Ω → ι → ℝ} {t0 : ℕ}
    (h120 : ∀ t, t0 ≤ t → ∀ ω, M t ω = Λmat S β J *ᵥ M (t - 1) ω + q t ω) :
    S.Et = 0 ∧ Λmat S β J = 0 ∧ ∀ t, t0 ≤ t → M t = q t := by
  have hΛ : Λmat S β J = 0 := eq_zero_of_rank_zero hk
  have hE : S.Et.rank = 0 := by rw [← rank_Λmat S hβ hK]; exact hk
  refine ⟨eq_zero_of_rank_zero hE, hΛ, fun t ht => funext fun ω => ?_⟩
  rw [h120 t ht ω, hΛ, zero_mulVec, zero_add]

end Woodford.OptimalPolicyRules.MultiplierLags
