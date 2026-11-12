/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureStability

/-!
# The perfect-foresight Assumption 8.1 does not give existence for every disturbance

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541). The open question
left by `OptimalRulesMeasureGeneral`: does the perfect-foresight Assumption 8.1 alone give a
bounded solution of (1.1) + (1.9) on every filtered probability space for every bounded adapted
disturbance? Equivalently (`OptimalRulesMeasureGeneral.m_exists_iff`): is the forecast-driven
state always bounded? A sufficient condition was that the unit-modulus left eigen-directions `e`
of `H` receive no forcing, `e'K^N_k = 0`.

## Answer: no

The problem `eBP` (`n_Z = n_z = 1`, `β = 1/2`): `Z_{t+1} = Z_t + z_t`,
`E_t z_{t+1} = Z_t + z_t + i_t + c_t`, loss `½(z_t² + i_t²)`.

* **perfect foresight** (`eB_pf`): Assumption 8.1 holds — the bounded solution is unique, with
  `z_0` pinned by the forward sum `U_0 = −∑_k 2^{−k} c_k` of `U = 2Z − 2M_{−1} + 3z`
  (`eB_pfSystem`, `eB_triple_eq`);
* `H` has the eigenvalue `1` with left eigenvector `e = (1, 2)` (`eB_Hgen_mulVec`,
  `eB_left_eig`, `eB_eigenvalue_one`), and this direction **receives forcing**: `e'K^N_0 = 1/5`
  (`eB_eKN`). So the conjectured `e'K^N_k = 0` fails (`eB_conjecture_false`); what the
  perfect-foresight bound does give is only the summability of the kernel
  (`OptimalRulesMeasureKernel.kernel_summable`).
* **fair-coin economy** (`eB_not_solvable`): with `c_t = ε_t` (i.i.d. `±1`) and zero initial
  conditions, **no bounded solution exists**, at any `t₀`. Along a solution `V = U + c` satisfies
  `V_t = ½E_tV_{t+1}`, so `V = 0`; then `L = −Z − 4M_{−1} + z` (the direction `e`) is a random
  walk, `L_{t+1} = L_t − ε_{t+1}/3`, whose second moment `k/9` is unbounded
  (`coin_walk_sq`). So the measure Assumption 8.1 fails (`eB_not_assumption81MB`) and the
  forecast-driven state is unbounded (`eB_xs_unbounded`).

The root condition (no eigenvalue of `H` on the unit circle,
`OptimalRulesMeasureGeneral.m_assumption81MB_of_noUnit`) is therefore not removable from the
existence theorem, and the exact condition remains `OptimalRulesMeasureGeneral.m_exists_iff`.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureCounterexample

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure ExpectationsMeasureIID OptimalRulesMeasure OptimalRulesMeasureKernel
  OptimalRulesMeasureGeneral OptimalRulesMeasureStability

/-! ### The problem -/

/-- Woodford (2003), eq. (1.1), p. 537: the structure of the counterexample —
`Z_{t+1} = Z_t + z_t` and `E_t z_{t+1} = Z_t + z_t + i_t + c_t` (`A₁₁ = A₁₂ = A₂₁ = A₂₂ = 1`,
`Ẽ = 1`, `B₂ = 1`). -/
noncomputable def eBSys : LinearRESystem Unit Unit where
  A11 := 1
  A12 := 1
  A21 := 1
  A22 := 1
  Et := 1
  B2 := fun _ => 1
  A22_isUnit := by simp
  B2_ne_zero := fun h => one_ne_zero (congrFun h ())

/-- Woodford (2003), eqs. (1.2)–(1.4), p. 537: the counterexample problem — targets `τ = (z, i)`,
`W = I`, `τ* = 0`, `β = 1/2`. -/
noncomputable def eBP : LQProblem Unit Unit (Fin 2) where
  sys := eBSys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := Matrix.of fun a b => if a = 0 then Sum.elim (fun _ => 0) (fun _ => 1) b else 0
  Ti := ![0, 1]
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), eq. (1.9), p. 541, for `eBP` (`p` = `E_t φ_{t+1}`, `q` = `φ_t`, `v` = `y_t`):
the `Z`, `z` and `i` columns `E_tξ_{t+1} + M_t − 2ξ_t = 0`, `E_tξ_{t+1} + M_t + z_t − 2M_{t−1} = 0`,
`M_t + i_t = 0`. -/
theorem eB_foc_iff (p q : Unit ⊕ Unit → ℝ) (v : (Unit ⊕ Unit) ⊕ Unit → ℝ) :
    eBP.sys.Atilᵀ *ᵥ p + eBP.Tᵀ *ᵥ (eBP.W *ᵥ (eBP.T *ᵥ v - eBP.τstar)) -
        eBP.β⁻¹ • (eBP.sys.Itilᵀ *ᵥ q) = 0 ↔
      p (Sum.inl ()) + p (Sum.inr ()) - 2 * q (Sum.inl ()) = 0 ∧
        p (Sum.inl ()) + p (Sum.inr ()) + v (Sum.inl (Sum.inr ())) - 2 * q (Sum.inr ()) = 0 ∧
        p (Sum.inr ()) + v (Sum.inr ()) = 0 := by
  set F := eBP.sys.Atilᵀ *ᵥ p + eBP.Tᵀ *ᵥ (eBP.W *ᵥ (eBP.T *ᵥ v - eBP.τstar)) -
    eBP.β⁻¹ • (eBP.sys.Itilᵀ *ᵥ q) with hF
  have h0 : F (Sum.inl (Sum.inl ())) = p (Sum.inl ()) + p (Sum.inr ()) - 2 * q (Sum.inl ()) := by
    simp [hF, LQProblem.T, eBP, eBSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type]
  have h1 : F (Sum.inl (Sum.inr ())) =
      p (Sum.inl ()) + p (Sum.inr ()) + v (Sum.inl (Sum.inr ())) - 2 * q (Sum.inr ()) := by
    simp [hF, LQProblem.T, eBP, eBSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type]
  have h2 : F (Sum.inr ()) = p (Sum.inr ()) + v (Sum.inr ()) := by
    simp [hF, LQProblem.T, eBP, eBSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two]
  constructor
  · intro h
    exact ⟨h0 ▸ congrFun h _, h1 ▸ congrFun h _, h2 ▸ congrFun h _⟩
  · rintro ⟨e0, e1, e2⟩
    funext idx
    rcases idx with (u | u) | u
    · rcases u
      rw [h0, e0]
      rfl
    · rcases u
      rw [h1, e1]
      rfl
    · rcases u
      rw [h2, e2]
      rfl

/-- Woodford (2003), eq. (1.1), p. 537, for `eBP`: the expectational row is
`w = Z + z + i + c` (`w` the forecast of `z_{t+1}`). -/
theorem eB_struct_iff (w Z z : Unit → ℝ) (i : ℝ) (cc : Unit → ℝ) :
    eBP.sys.Et *ᵥ w = eBP.sys.A21 *ᵥ Z + eBP.sys.A22 *ᵥ z + i • eBP.sys.B2 + cc ↔
      w () = Z () + z () + i + cc () := by
  have h : ∀ u : Unit, (eBP.sys.A21 *ᵥ Z + eBP.sys.A22 *ᵥ z + i • eBP.sys.B2 + cc) u =
      Z () + z () + i + cc () := by
    intro u
    rcases u
    simp [eBP, eBSys]
  have h0 : ∀ u : Unit, (eBP.sys.Et *ᵥ w) u = w () := by
    intro u
    rcases u
    simp [eBP, eBSys]
  constructor
  · intro e
    have := congrFun e ()
    rw [h, h0] at this
    exact this
  · intro e
    funext u
    rw [h, h0, e]

/-- Woodford (2003), eq. (1.1), p. 537, for `eBP`: the predetermined row is
`Z_{t+1} = Z_t + z_t`. -/
theorem eB_Zrow (Z z : Unit → ℝ) : eBP.sys.A11 *ᵥ Z + eBP.sys.A12 *ᵥ z = fun _ => Z () + z () := by
  funext u
  rcases u
  simp [eBP, eBSys]

/-! ### Perfect foresight: the explicit solution -/

/-- Woodford (2003), App. G (tool): the forward sum `U_t = −∑_k 2^{−k} g_{t+k}`, the bounded
solution of `U_{t+1} = 2U_t + 2g_t`. -/
noncomputable def fwd (g : ℕ → ℝ) (t : ℕ) : ℝ := -∑' k, (1 / 2 : ℝ) ^ k * g (t + k)

/-- Woodford (2003), fn 6, p. 539 (tool): the forward sum of a bounded path converges. -/
theorem fwd_summable {g : ℕ → ℝ} {K : ℝ} (hK : ∀ k, |g k| ≤ K) (t : ℕ) :
    Summable fun k => (1 / 2 : ℝ) ^ k * g (t + k) := by
  refine Summable.of_norm_bounded (g := fun k => K * (1 / 2 : ℝ) ^ k)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left K) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_comm]
  exact mul_le_mul_of_nonneg_right (hK _) (by positivity)

/-- Woodford (2003), App. G (tool): `U_{t+1} = 2U_t + 2g_t`. -/
theorem fwd_succ {g : ℕ → ℝ} {K : ℝ} (hK : ∀ k, |g k| ≤ K) (t : ℕ) :
    fwd g (t + 1) = 2 * fwd g t + 2 * g t := by
  have e := (fwd_summable hK t).tsum_eq_zero_add
  have e2 : (fun k => (1 / 2 : ℝ) ^ (k + 1) * g (t + (k + 1))) =
      fun k => (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * g (t + 1 + k)) := by
    funext k
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  rw [e2, tsum_mul_left] at e
  simp only [fwd, pow_zero, one_mul, add_zero] at e ⊢
  linarith

/-- Woodford (2003), fn 6, p. 539 (tool): `|U_t| ≤ 2K`. -/
theorem fwd_bdd {g : ℕ → ℝ} {K : ℝ} (hK : ∀ k, |g k| ≤ K) (t : ℕ) : |fwd g t| ≤ 2 * K := by
  have hg : HasSum (fun k => K * (1 / 2 : ℝ) ^ k) (2 * K) := by
    have := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left K
    convert this using 1
    norm_num
    ring
  have := tsum_of_norm_bounded (f := fun k => (1 / 2 : ℝ) ^ k * g (t + k)) hg fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_comm]
    exact mul_le_mul_of_nonneg_right (hK _) (by positivity)
  rw [fwd, abs_neg, ← Real.norm_eq_abs]
  exact this

/-- Woodford (2003), p. 541, for `eBP`: the conserved quantity of the perfect-foresight plan,
`L = −Z_0 − 4M_{−1} + z_0`, with `z_0 = (U_0 − 2Z_0 + 2M_{−1})/3`. -/
noncomputable def eBL (a b : ℝ) (g : ℕ → ℝ) : ℝ := -a - 4 * b + (fwd g 0 - 2 * a + 2 * b) / 3

/-- Woodford (2003), p. 541, for `eBP`: the coordinate `S_t = −Z_t + M_{t−1} + z_t` of the
perfect-foresight plan (`S_{t+1} = c_t`). -/
noncomputable def eBS (a b : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => -a + b + (fwd g 0 - 2 * a + 2 * b) / 3
  | t + 1 => g t

/-- Woodford (2003), (1.5), for `eBP` under perfect foresight from `(Z_0, M_{−1}) = (a, b)` with
forcing `g`: `Z_t = (U_t − 2S_t − L)/5`, `z_t = (U_t + 2S_t)/5`, `i_t = −(g_t − L)/5`. -/
noncomputable def eBy (a b : ℝ) (g : ℕ → ℝ) : ℕ → Unit → (Unit ⊕ Unit) ⊕ Unit → ℝ :=
  fun t _ => Sum.elim (Sum.elim (fun _ => (fwd g t - 2 * eBS a b g t - eBL a b g) / 5)
    (fun _ => (fwd g t + 2 * eBS a b g t) / 5)) (fun _ => -(g t - eBL a b g) / 5)

/-- Woodford (2003), (1.9), for `eBP` under perfect foresight: `ξ_t = −(U_t + 2L)/10`,
`M_{t−1} = (S_t − L)/5`. -/
noncomputable def eBφ (a b : ℝ) (g : ℕ → ℝ) : ℕ → Unit → Unit ⊕ Unit → ℝ :=
  fun t _ => Sum.elim (fun _ => -(fwd g t + 2 * eBL a b g) / 10)
    (fun _ => (eBS a b g t - eBL a b g) / 5)

/-- Woodford (2003), (1.1) + (1.9), p. 541, for `eBP` under perfect foresight: **the explicit
plan solves the system** for every bounded forcing path and all initial conditions. -/
theorem eB_pfSystem {c : ℕ → Unit → Unit → ℝ} (hcb : BoundedV c) (Z0 M0 : Unit → Unit → ℝ) :
    FOCSystem eBP perfectForesight c 0 Z0 M0
      (eBy (Z0 () ()) (M0 () ()) (fun k => c k () ()))
      (eBφ (Z0 () ()) (M0 () ()) (fun k => c k () ())) := by
  obtain ⟨K, hK⟩ := hcb
  have hg : ∀ k, |(fun k => c k () ()) k| ≤ K := fun k => hK k () ()
  have hsucc := fwd_succ hg
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hg 0)
  have hEV : ∀ {ι : Type} (t : ℕ) (x : Unit → ι → ℝ) (ω : Unit),
      EV perfectForesight t x ω = x ω := fun _ _ _ => rfl
  set a := Z0 () () with ha
  set b := M0 () () with hb
  set g : ℕ → ℝ := fun k => c k () () with hgdef
  set S0 := eBS a b g 0 with hS0
  set L := eBL a b g with hL
  have hS : ∀ t, |eBS a b g t| ≤ |S0| + K := by
    intro t
    rcases t with _ | t
    · exact le_add_of_nonneg_right hK0
    · exact (hg t).trans (le_add_of_nonneg_left (abs_nonneg _))
  set B := 2 * K + (|S0| + K) + |L| + K with hB
  have hcomp : ∀ t, |fwd g t| ≤ B ∧ |eBS a b g t| ≤ B ∧ |g t| ≤ B ∧ |L| ≤ B ∧
      0 ≤ |S0| + |L| + K := by
    intro t
    have h1 := fwd_bdd hg t
    have h2 := hS t
    have h3 := hg t
    refine ⟨by linarith [abs_nonneg S0, abs_nonneg L], by linarith [abs_nonneg L],
      by linarith [abs_nonneg S0, abs_nonneg L], by linarith [abs_nonneg S0], by positivity⟩
  refine ⟨⟨fun t _ ω => ⟨?_, ?_⟩, fun ω => ?_, ⟨B, fun t ω i => ?_⟩, fun _ _ => rfl⟩,
    ⟨B, fun t ω i => ?_⟩, fun _ _ => rfl, fun ω => ?_, fun t _ ω => ?_⟩
  · rw [eB_Zrow]
    funext u
    simp only [eBy, Zpart, zpart, Sum.elim_inl, Sum.elim_inr, eBS]
    rw [hsucc t]
    ring
  · refine (eB_struct_iff _ _ _ _ _).mpr ?_
    rw [hEV]
    rcases ω
    simp only [eBy, Zpart, zpart, ipart, Sum.elim_inl, Sum.elim_inr, eBS]
    rw [hsucc t]
    ring
  · funext u
    simp only [eBy, Zpart, Sum.elim_inl, eBS, eBL]
    ring
  · obtain ⟨h1, h2, h3, h4, -⟩ := hcomp t
    rw [abs_le] at h1 h2 h3 h4
    rcases i with (u | u) | u
    · simp only [eBy, Sum.elim_inl]
      rw [abs_le]
      constructor <;> linarith
    · simp only [eBy, Sum.elim_inl, Sum.elim_inr]
      rw [abs_le]
      constructor <;> linarith
    · simp only [eBy, Sum.elim_inr]
      rw [abs_le]
      constructor <;> linarith
  · obtain ⟨h1, h2, h3, h4, -⟩ := hcomp t
    rw [abs_le] at h1 h2 h3 h4
    rcases i with u | u
    · simp only [eBφ, Sum.elim_inl]
      rw [abs_le]
      constructor <;> linarith
    · simp only [eBφ, Sum.elim_inr]
      rw [abs_le]
      constructor <;> linarith
  · funext u
    simp only [eBφ, Mpart, Sum.elim_inr, eBS, eBL]
    ring
  · rw [hEV]
    refine (eB_foc_iff _ _ _).mpr ⟨?_, ?_, ?_⟩
    · simp only [eBφ, Sum.elim_inl, Sum.elim_inr, eBS]
      rw [hsucc t]
      ring
    · simp only [eBφ, eBy, Sum.elim_inl, Sum.elim_inr, eBS]
      rw [hsucc t]
      ring
    · simp only [eBφ, eBy, Sum.elim_inr, eBS]
      ring

/-- Woodford (2003), Assumption 8.1 (existence), p. 541, for `eBP` under perfect foresight. -/
theorem eB_solvable : FOCSolvable eBP perfectForesight 0 := fun _ Z0 M0 hcb _ _ _ =>
  ⟨_, _, eB_pfSystem hcb Z0 M0⟩

/-! ### Perfect foresight: uniqueness -/

/-- Woodford (2003), App. G (tool): a bounded path with `x_{t+1} = 2x_t` starts at zero. -/
theorem double_zero {x : ℕ → ℝ} {B : ℝ} (h : ∀ t, x (t + 1) = 2 * x t) (hb : ∀ t, |x t| ≤ B) :
    x 0 = 0 := by
  have hk : ∀ k, x k = 2 ^ k * x 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [h, ih, pow_succ]; ring
  by_contra hx
  have hpos : 0 < |x 0| := abs_pos.mpr hx
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (B / |x 0|) (by norm_num : (1 : ℝ) < 2)
  have h1 := hb k
  rw [hk, abs_mul, abs_pow, abs_two] at h1
  rw [div_lt_iff₀ hpos] at hk'
  linarith

/-- Woodford (2003), (1.1) + (1.9), p. 541, for `eBP` under perfect foresight: along any solution
(`Z`, `z`, `i` the plan, `ξ`, `M` the multipliers), `Z_{t+1} = Z_t + z_t`,
`5M_t = 4M_{t−1} + Z_t − z_t + c_t`, `z_{t+1} = 4M_t − 4M_{t−1} + 2z_t`, `ξ_t = M_{t−1} − z_t/2`,
`i_t = −M_t`, and `U = 2Z − 2M_{−1} + 3z` satisfies `U_{t+1} = 2U_t + 2c_t`. -/
theorem eB_derived {c : ℕ → Unit → Unit → ℝ} {Z0 M0 : Unit → Unit → ℝ}
    {y : ℕ → Unit → (Unit ⊕ Unit) ⊕ Unit → ℝ} {φ : ℕ → Unit → Unit ⊕ Unit → ℝ}
    (h : FOCSystem eBP perfectForesight c 0 Z0 M0 y φ) (t : ℕ) :
    y (t + 1) () (Sum.inl (Sum.inl ())) =
        y t () (Sum.inl (Sum.inl ())) + y t () (Sum.inl (Sum.inr ())) ∧
      5 * φ (t + 1) () (Sum.inr ()) = 4 * φ t () (Sum.inr ()) + y t () (Sum.inl (Sum.inl ())) -
        y t () (Sum.inl (Sum.inr ())) + c t () () ∧
      y (t + 1) () (Sum.inl (Sum.inr ())) = 4 * φ (t + 1) () (Sum.inr ()) -
        4 * φ t () (Sum.inr ()) + 2 * y t () (Sum.inl (Sum.inr ())) ∧
      φ t () (Sum.inl ()) = φ t () (Sum.inr ()) - y t () (Sum.inl (Sum.inr ())) / 2 ∧
      y t () (Sum.inr ()) = -φ (t + 1) () (Sum.inr ()) := by
  obtain ⟨⟨hst, -, -, -⟩, -, -, -, hfoc⟩ := h
  have hEV : ∀ {ι : Type} (t : ℕ) (x : Unit → ι → ℝ) (ω : Unit),
      EV perfectForesight t x ω = x ω := fun _ _ _ => rfl
  have foc : ∀ s, _ := fun s => (eB_foc_iff _ _ _).mp (hfoc s (Nat.zero_le s) ())
  simp only [hEV] at foc
  have R1 := congrFun (hst t (Nat.zero_le t) ()).1 ()
  rw [eB_Zrow] at R1
  have R2 := (eB_struct_iff _ _ _ _ _).mp (hst t (Nat.zero_le t) ()).2
  rw [hEV] at R2
  simp only [Zpart, zpart, ipart] at R1 R2
  obtain ⟨F1, F2, F3⟩ := foc t
  obtain ⟨G1, G2, -⟩ := foc (t + 1)
  refine ⟨R1, ?_, ?_, by linarith, by linarith⟩ <;> linarith

/-- Woodford (2003), App. G, for `eBP` under perfect foresight: along any solution,
`U = 2Z − 2M_{−1} + 3z` satisfies `U_{t+1} = 2U_t + 2c_t`. -/
theorem eB_U_succ {c : ℕ → Unit → Unit → ℝ} {Z0 M0 : Unit → Unit → ℝ}
    {y : ℕ → Unit → (Unit ⊕ Unit) ⊕ Unit → ℝ} {φ : ℕ → Unit → Unit ⊕ Unit → ℝ}
    (h : FOCSystem eBP perfectForesight c 0 Z0 M0 y φ) (t : ℕ) :
    2 * y (t + 1) () (Sum.inl (Sum.inl ())) - 2 * φ (t + 1) () (Sum.inr ()) +
        3 * y (t + 1) () (Sum.inl (Sum.inr ())) =
      2 * (2 * y t () (Sum.inl (Sum.inl ())) - 2 * φ t () (Sum.inr ()) +
        3 * y t () (Sum.inl (Sum.inr ()))) + 2 * c t () () := by
  obtain ⟨e1, e2, e3, -, -⟩ := eB_derived h t
  linarith

/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541, for `eBP` under perfect foresight: two
solutions with the same data have the same `(Z_t, M_{t−1}, z_t)` at every date (the difference of
`U` doubles each period and is bounded, so `z_0` is pinned). -/
theorem eB_triple_eq {c : ℕ → Unit → Unit → ℝ} {Z0 M0 : Unit → Unit → ℝ}
    {y y' : ℕ → Unit → (Unit ⊕ Unit) ⊕ Unit → ℝ} {φ φ' : ℕ → Unit → Unit ⊕ Unit → ℝ}
    (h : FOCSystem eBP perfectForesight c 0 Z0 M0 y φ)
    (h' : FOCSystem eBP perfectForesight c 0 Z0 M0 y' φ') (t : ℕ) :
    y t () (Sum.inl (Sum.inl ())) = y' t () (Sum.inl (Sum.inl ())) ∧
      φ t () (Sum.inr ()) = φ' t () (Sum.inr ()) ∧
      y t () (Sum.inl (Sum.inr ())) = y' t () (Sum.inl (Sum.inr ())) := by
  have hZ0 : y 0 () (Sum.inl (Sum.inl ())) = y' 0 () (Sum.inl (Sum.inl ())) :=
    (congrFun (h.1.2.1 ()) ()).trans (congrFun (h'.1.2.1 ()) ()).symm
  have hM0 : φ 0 () (Sum.inr ()) = φ' 0 () (Sum.inr ()) :=
    (congrFun (h.2.2.2.1 ()) ()).trans (congrFun (h'.2.2.2.1 ()) ()).symm
  obtain ⟨Ky, hKy⟩ := h.1.2.2.1
  obtain ⟨Ky', hKy'⟩ := h'.1.2.2.1
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  obtain ⟨Kφ', hKφ'⟩ := h'.2.1
  set W : ℕ → ℝ := fun t =>
    (2 * y t () (Sum.inl (Sum.inl ())) - 2 * φ t () (Sum.inr ()) +
      3 * y t () (Sum.inl (Sum.inr ()))) -
    (2 * y' t () (Sum.inl (Sum.inl ())) - 2 * φ' t () (Sum.inr ()) +
      3 * y' t () (Sum.inl (Sum.inr ()))) with hW
  have hW0 : W 0 = 0 := by
    refine double_zero (B := 5 * Ky + 2 * Kφ + 5 * Ky' + 2 * Kφ') (fun t => ?_) fun t => ?_
    · simp only [hW]
      rw [eB_U_succ h t, eB_U_succ h' t]
      ring
    · have a1 := abs_le.mp (hKy t () (Sum.inl (Sum.inl ())))
      have a2 := abs_le.mp (hKy t () (Sum.inl (Sum.inr ())))
      have a3 := abs_le.mp (hKφ t () (Sum.inr ()))
      have b1 := abs_le.mp (hKy' t () (Sum.inl (Sum.inl ())))
      have b2 := abs_le.mp (hKy' t () (Sum.inl (Sum.inr ())))
      have b3 := abs_le.mp (hKφ' t () (Sum.inr ()))
      rw [abs_le]
      simp only [hW]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, b1.1, b1.2, b2.1, b2.2,
        b3.1, b3.2]
  induction t with
  | zero =>
    refine ⟨hZ0, hM0, ?_⟩
    simp only [hW] at hW0
    rw [hZ0, hM0] at hW0
    linarith
  | succ t ih =>
    obtain ⟨e1, e2, e3, -, -⟩ := eB_derived h t
    obtain ⟨f1, f2, f3, -, -⟩ := eB_derived h' t
    obtain ⟨i1, i2, i3⟩ := ih
    have hm : φ (t + 1) () (Sum.inr ()) = φ' (t + 1) () (Sum.inr ()) := by
      rw [i1, i2, i3] at e2
      linarith
    refine ⟨by rw [e1, f1, i1, i3], hm, by rw [e3, f3, hm, i2, i3]⟩

/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541, for `eBP` under perfect foresight. -/
theorem eB_unique : FOCUnique eBP perfectForesight 0 := by
  intro c Z0 M0 y y' φ φ' h h' t _
  obtain ⟨i1, i2, i3⟩ := eB_triple_eq h h' t
  obtain ⟨j1, j2, j3⟩ := eB_triple_eq h h' (t + 1)
  obtain ⟨-, -, -, d4, d5⟩ := eB_derived h t
  obtain ⟨-, -, -, d4', d5'⟩ := eB_derived h' t
  refine ⟨funext fun ω => funext fun idx => ?_, funext fun ω => funext fun idx => ?_⟩
  · rcases ω
    rcases idx with (u | u) | u <;> rcases u
    · exact i1
    · exact i3
    · rw [d5, d5', j2]
  · rcases ω
    rcases idx with u | u <;> rcases u
    · rw [d4, d4', i2, i3]
    · exact i2

/-- Woodford (2003), **Assumption 8.1 under perfect foresight**, p. 541, for `eBP`: for every
bounded forcing path and all initial conditions (1.1) + (1.9) has exactly one bounded solution. -/
theorem eB_pf : Assumption81 eBP perfectForesight 0 := ⟨eB_solvable, eB_unique⟩

/-! ### The state transition `H` and the kernel -/

/-- Woodford (2003), Assumption 8.1, p. 541, for `eBP`: the bounded perfect-foresight solution
(`OptimalRulesMeasureKernel.solY`, `solΦ`) is the explicit plan. -/
theorem eB_sol (n : Unit ⊕ Unit → ℝ) {g : ℕ → Unit → ℝ} (hg : BddSeq g) (k : ℕ) :
    solY eB_pf n g k = eBy (n (Sum.inl ())) (n (Sum.inr ())) (fun k => g k ()) k () ∧
      solΦ eB_pf n g k = eBφ (n (Sum.inl ())) (n (Sum.inr ())) (fun k => g k ()) k () := by
  obtain ⟨K, hK⟩ := hg
  have h := sol_unique eB_pf ⟨K, hK⟩
    (eB_pfSystem (c := fun k _ => g k) ⟨K, fun k _ i => hK k i⟩ (fun _ j => n (Sum.inl j))
      (fun _ r => n (Sum.inr r))) k
  exact ⟨h.1.symm, h.2.symm⟩

/-- Woodford (2003), App. G (tool): the forward sum of the zero path is zero. -/
theorem fwd_zero (t : ℕ) : fwd (fun k => (0 : ℕ → Unit → ℝ) k ()) t = 0 := by
  simp [fwd]

/-- Woodford (2003), p. 539, for `eBP`: with zero forcing the next state is
`(Z_1, M_0) = ((Z_0 + 2M_{−1})/3, (Z_0 + 2M_{−1})/3)`. -/
theorem eB_nextS0 (n : Unit ⊕ Unit → ℝ) :
    nextS eB_pf n 0 = fun _ => (n (Sum.inl ()) + 2 * n (Sum.inr ())) / 3 := by
  funext x
  rcases x with u | u <;> rcases u
  · simp only [nextS, Sum.elim_inl, Zpart, (eB_sol n (bddSeq_zero (ι := Unit)) 1).1, eBy, eBS,
      eBL, fwd_zero]
    simp
    ring
  · simp only [nextS, Sum.elim_inr, Mpart, (eB_sol n (bddSeq_zero (ι := Unit)) 1).2, eBφ, eBS,
      eBL, fwd_zero]
    simp
    ring

/-- Woodford (2003), p. 539, for `eBP`: `H n = ((n_Z + 2n_M)/3, (n_Z + 2n_M)/3)`. -/
theorem eB_Hgen_mulVec (n : Unit ⊕ Unit → ℝ) :
    Hgen eB_pf *ᵥ n = fun _ => (n (Sum.inl ()) + 2 * n (Sum.inr ())) / 3 := by
  have e1 := hgen_spec eB_pf n
  have e0 := hgen_spec eB_pf 0
  rw [mulVec_zero, add_zero] at e0
  have : Hgen eB_pf *ᵥ n = nextS eB_pf n 0 - nextS eB_pf 0 0 := by
    rw [e1, e0]
    abel
  rw [this, eB_nextS0, eB_nextS0]
  funext x
  simp

/-- Woodford (2003), p. 539, for `eBP`: `H = [1/3 2/3; 1/3 2/3]`. -/
theorem eB_Hgen :
    Hgen eB_pf = Matrix.of fun _ j => Sum.elim (fun _ => 1 / 3) (fun _ => 2 / 3) j := by
  ext i j
  have := congrFun (eB_Hgen_mulVec (Pi.single j (1 : ℝ))) i
  rw [mulVec_single_one] at this
  have h2 : Hgen eB_pf i j = ((Pi.single j (1 : ℝ) : Unit ⊕ Unit → ℝ) (Sum.inl ()) +
      2 * (Pi.single j (1 : ℝ) : Unit ⊕ Unit → ℝ) (Sum.inr ())) / 3 := this
  rw [h2]
  rcases j with u | u <;> rcases u <;> simp

/-- Woodford (2003), p. 539, for `eBP`: the left eigen-direction `e = (1, 2)` of `H` for the
eigenvalue `1` (`e'H = e'`): `Z_t + 2M_{t−1}` is conserved under perfect foresight with zero
forcing. -/
theorem eB_left_eig :
    Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* Hgen eB_pf =
      Sum.elim (fun _ => 1) (fun _ => 2) := by
  rw [eB_Hgen]
  funext j
  rcases j with u | u <;> rcases u <;>
    simp [vecMul, dotProduct, Fintype.sum_sum_type] <;> norm_num

/-- Woodford (2003), p. 539, for `eBP`: **`H` has the eigenvalue `1`** (right eigenvector
`(1, 1)`). -/
theorem eB_eigenvalue_one :
    (Matrix.scalar (Unit ⊕ Unit) (1 : ℂ) - (Hgen eB_pf).map Complex.ofReal).det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨fun i => ((Sum.elim (fun _ => (1 : ℝ)) (fun _ => 1) i : ℝ) : ℂ), fun h => ?_, ?_⟩
  · have := congrFun h (Sum.inl ())
    simp at this
  · rw [sub_mulVec, GeneralBKCopy.map_ofReal_mulVec, eB_Hgen_mulVec]
    funext i
    rcases i with u | u <;> rcases u <;> simp [Matrix.scalar_apply] <;> norm_num

/-- Woodford (2003), p. 539, for `eBP`: `H` is not geometrically stable (although the
perfect-foresight Assumption 8.1 holds, `eB_pf`). -/
theorem eB_not_powDecay : ¬ PencilSplit.PowDecay (Hgen eB_pf) := fun hd =>
  noUnit_of_powDecay hd 1 (by simp) eB_eigenvalue_one

/-- Woodford (2003), App. G (tool): the unit impulse at date `0` as a scalar path. -/
theorem imp_scalar (k : ℕ) : imp 0 () k () = if k = 0 then (1 : ℝ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [imp]
  · simp [imp, hk]

/-- Woodford (2003), p. 539, for `eBP`: the next-state kernel at lag `0`,
`K^N_0 = (−1/3, 4/15)` — the response of `(Z_1, M_0)` to a unit `c_0`. -/
theorem eB_KN0 :
    KN eB_pf 0 = Matrix.of fun a _ => Sum.elim (fun _ => -1 / 3) (fun _ => 4 / 15) a := by
  have hb : ∀ k, |(fun k => imp 0 () k ()) k| ≤ 1 := fun k => by
    simp only [imp_scalar]
    split_ifs <;> simp
  have hf0 : fwd (fun k => imp 0 () k ()) 0 = -1 := by
    rw [fwd, tsum_eq_single 0 fun k hk => by simp [imp_scalar, hk]]
    simp [imp_scalar]
  have hf1 : fwd (fun k => imp 0 () k ()) 1 = 0 := by
    rw [fwd_succ hb 0, hf0, imp_scalar]
    norm_num
  have hg0 : imp 0 () 0 () = (1 : ℝ) := by simp [imp_scalar]
  ext a i
  rcases i
  rcases a with u | u <;> rcases u
  · simp only [KN, KY, Matrix.of_apply, Sum.elim_inl,
      (eB_sol 0 (bddSeq_imp 0 ()) 1).1, (eB_sol 0 (bddSeq_zero (ι := Unit)) 1).1, eBy, eBS, eBL,
      fwd_zero, hf0, hf1, hg0]
    norm_num
  · simp only [KN, KΦ, Matrix.of_apply, Sum.elim_inr,
      (eB_sol 0 (bddSeq_imp 0 ()) 1).2, (eB_sol 0 (bddSeq_zero (ι := Unit)) 1).2, eBφ, eBS, eBL,
      fwd_zero, hf0, hg0]
    norm_num

/-- Woodford (2003), p. 539, for `eBP`: **the unit-modulus left eigen-direction `e = (1, 2)` of
`H` receives forcing**, `e'K^N_0 = 1/5 ≠ 0`. -/
theorem eB_eKN : Sum.elim (fun _ => (1 : ℝ)) (fun _ => 2) ᵥ* KN eB_pf 0 = fun _ => 1 / 5 := by
  rw [eB_KN0]
  funext j
  simp [vecMul, dotProduct, Fintype.sum_sum_type]
  norm_num

/-- Woodford (2003), Assumption 8.1, p. 541: **the conjecture "unit-modulus left
eigen-directions of `H` receive no forcing" is false** — in `eBP` (where the perfect-foresight
Assumption 8.1 holds, `eB_pf`) there is a left eigenvector `e` of `H` for the eigenvalue `1`
with `e'K^N_0 ≠ 0`. -/
theorem eB_conjecture_false :
    ∃ e : Unit ⊕ Unit → ℝ, e ≠ 0 ∧ e ᵥ* Hgen eB_pf = e ∧ e ᵥ* KN eB_pf 0 ≠ 0 := by
  refine ⟨Sum.elim (fun _ => 1) (fun _ => 2), fun h => ?_, eB_left_eig, fun h => ?_⟩
  · have := congrFun h (Sum.inl ())
    simp at this
  · rw [eB_eKN] at h
    have := congrFun h ()
    norm_num at this

/-! ### The fair-coin economy: the random walk -/

/-- Woodford (2003), fn 6, p. 539 (tool; the fair-coin economy of Cochrane (2023), Ch. 2): the
coins are a.s. bounded by one at every date. -/
theorem coin_shock_bdd : ∀ᵐ ω ∂(iidSystem coin).μ, ∀ j, |shock j ω| ≤ 1 :=
  ae_all_iff.2 fun j => shock_ae_bdd coin coin_bdd j

/-- Woodford (2003), p. 540 (tool): the coin random walk `X_k = ∑_{j<k} ε_{s+1+j}` is known at
`s + k`. -/
theorem walk_sm (s k : ℕ) : StronglyMeasurable[(iidSystem coin).𝓕 (s + k)]
    (fun ω => ∑ j ∈ Finset.range k, shock (s + 1 + j) ω) :=
  Finset.stronglyMeasurable_fun_sum _ fun j hj =>
    (measurable_shock coin (by have := Finset.mem_range.mp hj; omega)).stronglyMeasurable

/-- Woodford (2003), fn 6 (tool): `|X_k| ≤ k` a.s. -/
theorem walk_bdd (s k : ℕ) : ∀ᵐ ω ∂(iidSystem coin).μ,
    |∑ j ∈ Finset.range k, shock (s + 1 + j) ω| ≤ k := by
  filter_upwards [coin_shock_bdd] with ω h
  calc |∑ j ∈ Finset.range k, shock (s + 1 + j) ω|
      ≤ ∑ j ∈ Finset.range k, |shock (s + 1 + j) ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum fun j _ => h _
    _ = k := by simp

/-- Woodford (2003), p. 540 (tool; the fair-coin economy of Cochrane (2023), Ch. 2): **the second
moment of the coin random walk**,
`E[(ε_{s+1} + ⋯ + ε_{s+k})²] = k` (the cross terms vanish by the law of iterated expectations
and `E_t ε_{t+1} = 0`). -/
theorem coin_walk_sq (s k : ℕ) :
    ∫ ω, (∑ j ∈ Finset.range k, shock (s + 1 + j) ω) ^ 2 ∂(iidSystem coin).μ = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    set S := iidSystem coin with hS
    set X : (ℕ → ℝ) → ℝ := fun ω => ∑ j ∈ Finset.range k, shock (s + 1 + j) ω with hX
    set ξ : (ℕ → ℝ) → ℝ := shock (s + k + 1) with hξ
    have hsum : (fun ω => (∑ j ∈ Finset.range (k + 1), shock (s + 1 + j) ω) ^ 2) =
        fun ω => X ω ^ 2 + 2 * (X ω * ξ ω) + ξ ω ^ 2 := by
      funext ω
      rw [Finset.sum_range_succ, show s + 1 + k = s + k + 1 by omega]
      ring
    have hXm : StronglyMeasurable[S.𝓕 (s + k)] X := walk_sm s k
    have hXb : ∀ᵐ ω ∂S.μ, |X ω| ≤ k := walk_bdd s k
    have hξm : Measurable ξ := measurable_pi_apply _
    have hξb : ∀ᵐ ω ∂S.μ, |ξ ω| ≤ 1 := shock_ae_bdd coin coin_bdd _
    have hXa : AEStronglyMeasurable X S.μ := (hXm.mono (S.𝓕.le _)).aestronglyMeasurable
    have hξi : Integrable ξ S.μ := integrable_of_bound hξm.aestronglyMeasurable hξb
    have hX2 : Integrable (fun ω => X ω ^ 2) S.μ := by
      refine integrable_of_bound (K := (k : ℝ) ^ 2) (hXa.pow 2) ?_
      filter_upwards [hXb] with ω h
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hXξ : Integrable (fun ω => X ω * ξ ω) S.μ := by
      refine integrable_of_bound (K := (k : ℝ) * 1) (hXa.mul hξm.aestronglyMeasurable) ?_
      filter_upwards [hXb, hξb] with ω h1 h2
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) (Nat.cast_nonneg _)
    have hξ2 : Integrable (fun ω => ξ ω ^ 2) S.μ := by
      refine integrable_of_bound (K := 1) (hξm.aestronglyMeasurable.pow 2) ?_
      filter_upwards [hξb] with ω h
      rw [abs_pow]
      calc |ξ ω| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = 1 := one_pow 2
    have hcross : ∫ ω, X ω * ξ ω ∂S.μ = 0 := by
      have h1 : S.E (s + k) (X * ξ) =ᵐ[S.μ] X * S.E (s + k) ξ := S.E_pullOut hXm hXb hξi
      have h2 : S.E (s + k) ξ =ᵐ[S.μ] 0 := E_shock_zero coin_mean (s + k)
      calc ∫ ω, X ω * ξ ω ∂S.μ = ∫ ω, S.E (s + k) (X * ξ) ω ∂S.μ :=
            (S.integral_E (s + k) (X * ξ)).symm
        _ = ∫ _ω, (0 : ℝ) ∂S.μ := by
            refine integral_congr_ae ?_
            filter_upwards [h1, h2] with ω e1 e2
            rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]
        _ = 0 := integral_zero _ _
    have hsq : ∫ ω, ξ ω ^ 2 ∂S.μ = 1 := by
      have := integral_shock_fun coin (s + k + 1) (f := fun x => x ^ 2)
        (measurable_id.pow_const 2)
      rw [coin_var] at this
      exact this
    have h2c : Integrable (fun ω => 2 * (X ω * ξ ω)) S.μ := hXξ.const_mul 2
    have h12 : Integrable (fun ω => X ω ^ 2 + 2 * (X ω * ξ ω)) S.μ := hX2.add h2c
    rw [hsum, integral_add h12 hξ2, integral_add hX2 h2c, integral_const_mul, hcross, hsq, ih]
    push_cast
    ring

/-! ### The fair-coin economy: no bounded solution -/

/-- Woodford (2003), (1.1) + (1.9), p. 541, for `eBP` on the fair-coin economy with `c_t = ε_t`:
along any bounded solution, `V = 2Z − 2M_{−1} + 3z + c` satisfies `V_t = ½E_tV_{t+1}`, hence
vanishes, and then `L = −Z − 4M_{−1} + z` is a random walk, `L_{t+1} = L_t − ε_{t+1}/3` a.s. -/
theorem eB_coin_L {t0 : ℕ} {Z0 M0 : (ℕ → ℝ) → Unit → ℝ}
    {y : ℕ → (ℕ → ℝ) → (Unit ⊕ Unit) ⊕ Unit → ℝ} {φ : ℕ → (ℕ → ℝ) → Unit ⊕ Unit → ℝ}
    (h : MFOCSystem (iidSystem coin) eBP (fun t ω _ => shock t ω) t0 Z0 M0 y φ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂(iidSystem coin).μ,
      -y (t + 1) ω (Sum.inl (Sum.inl ())) - 4 * φ (t + 1) ω (Sum.inr ()) +
          y (t + 1) ω (Sum.inl (Sum.inr ())) =
        -y t ω (Sum.inl (Sum.inl ())) - 4 * φ t ω (Sum.inr ()) + y t ω (Sum.inl (Sum.inr ())) -
          shock (t + 1) ω / 3 := by
  set S := iidSystem coin with hS
  obtain ⟨⟨hst, -, ⟨Ky, hKy⟩, hya⟩, ⟨Kφ, hKφ⟩, hφm, hMM, -, hfoc⟩ := h
  have hyi : ∀ t i, Integrable (fun ω => y t ω i) S.μ := fun t i =>
    integrable_of_bound ((hya t i).mono (S.𝓕.le t)).aestronglyMeasurable
      ((hKy t).mono fun ω hh => hh i)
  have hφi : ∀ t i, Integrable (fun ω => φ t ω i) S.μ := fun t i =>
    integrable_of_bound (hφm t i) ((hKφ t).mono fun ω hh => hh i)
  have hMk : ∀ t, S.E t (fun ω => φ (t + 1) ω (Sum.inr ())) = fun ω => φ (t + 1) ω (Sum.inr ()) :=
    fun t => S.E_of_stronglyMeasurable (hMM t ()) (hφi _ _)
  have hsi : ∀ t, Integrable (shock t) S.μ := fun t =>
    integrable_of_bound (measurable_pi_apply _).aestronglyMeasurable (shock_ae_bdd coin coin_bdd t)
  have R1 : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, y (t + 1) ω (Sum.inl (Sum.inl ())) =
      y t ω (Sum.inl (Sum.inl ())) + y t ω (Sum.inl (Sum.inr ())) := by
    intro t ht
    filter_upwards [(hst t ht).1] with ω e
    rw [eB_Zrow] at e
    exact congrFun e ()
  have R2 : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      S.E t (fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr ()))) ω =
        y t ω (Sum.inl (Sum.inl ())) + y t ω (Sum.inl (Sum.inr ())) + y t ω (Sum.inr ()) +
          shock t ω := by
    intro t ht
    filter_upwards [(hst t ht).2] with ω e
    exact (eB_struct_iff _ _ _ _ _).mp e
  have F : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      S.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω + φ (t + 1) ω (Sum.inr ()) -
          2 * φ t ω (Sum.inl ()) = 0 ∧
        S.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω + φ (t + 1) ω (Sum.inr ()) +
          y t ω (Sum.inl (Sum.inr ())) - 2 * φ t ω (Sum.inr ()) = 0 ∧
        φ (t + 1) ω (Sum.inr ()) + y t ω (Sum.inr ()) = 0 := by
    intro t ht
    filter_upwards [hfoc t ht] with ω e
    have e' := (eB_foc_iff _ _ _).mp e
    have hm : EVm S t (φ (t + 1)) ω (Sum.inr ()) = φ (t + 1) ω (Sum.inr ()) :=
      congrFun (hMk t) ω
    rw [hm] at e'
    exact e'
  have hξ : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      φ t ω (Sum.inl ()) = φ t ω (Sum.inr ()) - y t ω (Sum.inl (Sum.inr ())) / 2 := by
    intro t ht
    filter_upwards [F t ht] with ω e
    linarith [e.1, e.2.1]
  have hEξ : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, S.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω =
      φ (t + 1) ω (Sum.inr ()) - S.E t (fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr ()))) ω / 2 := by
    intro t ht
    have hc : (fun ω' => φ (t + 1) ω' (Sum.inl ())) =ᵐ[S.μ]
        (fun ω' => φ (t + 1) ω' (Sum.inr ())) -
          (1 / 2 : ℝ) • fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr ())) := by
      filter_upwards [hξ (t + 1) (by omega)] with ω e
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e]
      ring
    filter_upwards [S.E_congr hc t, S.E_sub (hφi (t + 1) _) ((hyi (t + 1) _).smul (1 / 2 : ℝ)) t,
      S.E_smul (1 / 2 : ℝ) (fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr ()))) t] with ω e1 e2 e3
    rw [e1, e2, Pi.sub_apply, e3, hMk t, Pi.smul_apply, smul_eq_mul]
    ring
  have hEz : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      S.E t (fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr ()))) ω =
        4 * φ (t + 1) ω (Sum.inr ()) - 4 * φ t ω (Sum.inr ()) +
          2 * y t ω (Sum.inl (Sum.inr ())) := by
    intro t ht
    filter_upwards [F t ht, hEξ t ht, hξ t ht] with ω e1 e2 e3
    linarith [e1.1]
  have hm : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      5 * φ (t + 1) ω (Sum.inr ()) = 4 * φ t ω (Sum.inr ()) + y t ω (Sum.inl (Sum.inl ())) -
        y t ω (Sum.inl (Sum.inr ())) + shock t ω := by
    intro t ht
    filter_upwards [R2 t ht, F t ht, hEz t ht] with ω e1 e2 e3
    linarith [e2.2.2]
  set Vt : ℕ → (ℕ → ℝ) → ℝ := fun t ω => 2 * y t ω (Sum.inl (Sum.inl ())) -
    2 * φ t ω (Sum.inr ()) + 3 * y t ω (Sum.inl (Sum.inr ())) + shock t ω with hVt
  have hEV : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, S.E t (Vt (t + 1)) ω =
      2 * (y t ω (Sum.inl (Sum.inl ())) + y t ω (Sum.inl (Sum.inr ()))) -
        2 * φ (t + 1) ω (Sum.inr ()) +
        3 * S.E t (fun ω' => y (t + 1) ω' (Sum.inl (Sum.inr ()))) ω := by
    intro t ht
    set A : (ℕ → ℝ) → ℝ := fun ω => 2 * (y t ω (Sum.inl (Sum.inl ())) +
      y t ω (Sum.inl (Sum.inr ()))) - 2 * φ (t + 1) ω (Sum.inr ()) with hA
    have hAm : StronglyMeasurable[S.𝓕 t] A :=
      (((hya t _).add (hya t _)).const_mul 2).sub ((hMM t ()).const_mul 2)
    have hAi : Integrable A S.μ :=
      (((hyi t _).add (hyi t _)).const_mul 2).sub ((hφi (t + 1) _).const_mul 2)
    have hc : Vt (t + 1) =ᵐ[S.μ]
        (A + (3 : ℝ) • fun ω => y (t + 1) ω (Sum.inl (Sum.inr ()))) + shock (t + 1) := by
      filter_upwards [R1 t ht] with ω e
      simp only [hVt, hA, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [e]
    filter_upwards [S.E_congr hc t, S.E_add (hAi.add ((hyi (t + 1) _).smul (3 : ℝ))) (hsi _) t,
      S.E_add hAi ((hyi (t + 1) _).smul (3 : ℝ)) t,
      S.E_smul (3 : ℝ) (fun ω => y (t + 1) ω (Sum.inl (Sum.inr ()))) t,
      E_shock_zero coin_mean t] with ω e1 e2 e3 e4 e5
    rw [e1, e2, Pi.add_apply, e3, Pi.add_apply, e4, Pi.smul_apply, smul_eq_mul, e5,
      Pi.zero_apply, S.E_of_stronglyMeasurable hAm hAi]
    simp only [hA]
    ring
  have hhalf : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Vt t ω = (1 / 2) * S.E t (Vt (t + 1)) ω := by
    intro t ht
    filter_upwards [hEV t ht, hEz t ht, hm t ht] with ω e1 e2 e3
    rw [e1, e2]
    simp only [hVt]
    linarith
  have hb : ∀ t, ∀ᵐ ω ∂S.μ, |Vt t ω| ≤ 5 * Ky + 2 * Kφ + 1 := by
    intro t
    filter_upwards [hKy t, hKφ t, shock_ae_bdd coin coin_bdd t] with ω h1 h2 h3
    have a1 := abs_le.mp (h1 (Sum.inl (Sum.inl ())))
    have a2 := abs_le.mp (h1 (Sum.inl (Sum.inr ())))
    have a3 := abs_le.mp (h2 (Sum.inr ()))
    have a4 := abs_le.mp h3
    simp only [hVt]
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]
  have hV0 := half_forward_zero hb hhalf
  intro t ht
  filter_upwards [R1 t ht, hm t ht, hV0 t ht, hV0 (t + 1) (by omega)] with ω e1 e2 e3 e4
  simp only [hVt] at e3 e4
  linarith

/-- Woodford (2003), Assumption 8.1, p. 541: **on the fair-coin economy, with `c_t = ε_t`, the
problem `eBP` has no bounded solution of (1.1) + (1.9), whatever the initial conditions and the
starting date** — although the perfect-foresight Assumption 8.1 holds (`eB_pf`). -/
theorem eB_no_solution (t0 : ℕ) (Z0 M0 : (ℕ → ℝ) → Unit → ℝ) :
    ¬ ∃ y φ, MFOCSystem (iidSystem coin) eBP (fun t ω _ => shock t ω) t0 Z0 M0 y φ := by
  rintro ⟨y, φ, h⟩
  have hL := eB_coin_L h
  obtain ⟨Ky, hKy⟩ := h.1.2.2.1
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  set Lt : ℕ → (ℕ → ℝ) → ℝ := fun t ω => -y t ω (Sum.inl (Sum.inl ())) -
    4 * φ t ω (Sum.inr ()) + y t ω (Sum.inl (Sum.inr ())) with hLt
  have hk : ∀ k, ∀ᵐ ω ∂(iidSystem coin).μ,
      Lt (t0 + k) ω = Lt t0 ω - (∑ j ∈ Finset.range k, shock (t0 + 1 + j) ω) / 3 := by
    intro k
    induction k with
    | zero => exact Eventually.of_forall fun ω => by simp
    | succ k ih =>
      filter_upwards [ih, hL (t0 + k) (by omega)] with ω e1 e2
      rw [Finset.sum_range_succ, show t0 + 1 + k = t0 + k + 1 by omega,
        show t0 + (k + 1) = t0 + k + 1 by omega]
      simp only [hLt] at e1 ⊢
      linarith
  set B := 6 * (2 * Ky + 4 * Kφ) with hB
  have hbd : ∀ k, ∀ᵐ ω ∂(iidSystem coin).μ,
      |∑ j ∈ Finset.range k, shock (t0 + 1 + j) ω| ≤ B := by
    intro k
    filter_upwards [hk k, hKy (t0 + k), hKφ (t0 + k), hKy t0, hKφ t0] with ω e h1 h2 h3 h4
    have a1 := abs_le.mp (h1 (Sum.inl (Sum.inl ())))
    have a2 := abs_le.mp (h1 (Sum.inl (Sum.inr ())))
    have a3 := abs_le.mp (h2 (Sum.inr ()))
    have b1 := abs_le.mp (h3 (Sum.inl (Sum.inl ())))
    have b2 := abs_le.mp (h3 (Sum.inl (Sum.inr ())))
    have b3 := abs_le.mp (h4 (Sum.inr ()))
    simp only [hLt] at e
    rw [abs_le]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, b1.1, b1.2, b2.1, b2.2, b3.1,
      b3.2]
  obtain ⟨k, hk'⟩ := exists_nat_gt (B ^ 2)
  have hint : Integrable (fun ω => (∑ j ∈ Finset.range k, shock (t0 + 1 + j) ω) ^ 2)
      (iidSystem coin).μ := by
    refine integrable_of_bound (K := (k : ℝ) ^ 2)
      ((((walk_sm t0 k).mono ((iidSystem coin).𝓕.le _)).aestronglyMeasurable).pow 2) ?_
    filter_upwards [walk_bdd t0 k] with ω h
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hle := integral_mono_ae hint (integrable_const (B ^ 2)) (by
    filter_upwards [hbd k] with ω h
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2)
  rw [coin_walk_sq t0 k] at hle
  simp at hle
  linarith

/-- Woodford (2003), Assumption 8.1 (existence), p. 541: it fails for `eBP` on the fair-coin
economy at every starting date. -/
theorem eB_not_solvable (t0 : ℕ) : ¬ MFOCSolvableMB (iidSystem coin) eBP t0 := fun hsol =>
  eB_no_solution t0 0 0 (hsol (fun t ω _ => shock t ω) 0 0
    ⟨1, fun t => (shock_ae_bdd coin coin_bdd t).mono fun _ hω _ => hω⟩
    (fun _ _ => (measurable_shock coin le_rfl).stronglyMeasurable)
    (fun _ => stronglyMeasurable_const) ⟨0, Eventually.of_forall fun _ _ => by simp⟩
    ⟨0, Eventually.of_forall fun _ _ => by simp⟩ (fun _ => stronglyMeasurable_const))

/-- Woodford (2003), **Assumption 8.1**, p. 541: the (corrected) measure form fails for `eBP` on
the fair-coin economy at every starting date. -/
theorem eB_not_assumption81MB (t0 : ℕ) : ¬ MAssumption81MB (iidSystem coin) eBP t0 := fun h =>
  eB_not_solvable t0 h.solvable

/-- Woodford (2003), Assumption 8.1, p. 541, and `OptimalRulesMeasureGeneral.m_exists_iff`: for
`eBP` on the fair-coin economy with `c_t = ε_t` and zero initial conditions **the
forecast-driven state is not essentially bounded** — the exact existence condition fails. -/
theorem eB_xs_unbounded (t0 : ℕ) :
    ¬ ∃ K, ∀ k, ∀ᵐ ω ∂(iidSystem coin).μ,
      ∀ i, |Xs eB_pf (iidSystem coin) (fun t ω _ => shock t ω) t0 0 0 k ω i| ≤ K := fun hX =>
  eB_no_solution t0 0 0 ((m_exists_iff eB_pf
    ⟨1, fun t => (shock_ae_bdd coin coin_bdd t).mono fun _ hω _ => hω⟩
    (fun _ _ => (measurable_shock coin le_rfl).stronglyMeasurable)
    (fun _ => stronglyMeasurable_const) (fun _ => stronglyMeasurable_const)).mpr hX)

/-- Woodford (2003), **Assumption 8.1**, p. 541: **the perfect-foresight Assumption 8.1 does
not imply the measure Assumption 8.1** — `eBP` satisfies the former (`eB_pf`) and violates the
latter on the fair-coin economy at every starting date (`eB_not_assumption81MB`); its `H` has the
eigenvalue `1` (`eB_eigenvalue_one`), so the root condition of
`OptimalRulesMeasureGeneral.m_assumption81MB_of_noUnit` cannot be dropped. -/
theorem pf_assumption81_not_sufficient :
    ∃ P : LQProblem Unit Unit (Fin 2), Assumption81 P perfectForesight 0 ∧
      ∀ t0, ¬ MAssumption81MB (iidSystem coin) P t0 :=
  ⟨eBP, eB_pf, eB_not_assumption81MB⟩

end Woodford.OptimalPolicyRules.OptimalRulesMeasureCounterexample
