/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigmaCE
import StabilizationWelfare.ExpectationsMeasureIID
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Smooth dependence on the shock scale with general bounded-support shocks

Woodford (2003), *Interest and Prices*, Appendix E.2, p. 695 (the policy function, the event
tree and the perturbation method), for shock laws with a CONTINUUM of values.

The unknowns are bounded families `u(t, s)` on dates and histories `s = ((r_t, ε_t), …)` of
(regime, shock) pairs, measurable in the history at each date and with finite memory (`adSub`,
a closed subspace of `ℓ∞`, hence a Banach space). The next regime is drawn from a Markov matrix
and the next shock from an ARBITRARY probability law of the new regime (node-dependent
innovation probabilities); a single regime is the i.i.d. case. Shocks enter through
`σ clip_B(ε)`, which is the identity on supports inside `[−B, B]`. The equilibrium map
`Φ(p, u)(t, s) = ∑_{r'} P(r_t, r') ∫ f(u(t + 1, (r', e) :: s), u(t, s), u_{t−1}, e_t, σ clip(e))
dν_{r'}(e)` is `Cᵏ` (Nemytskii operator into the closed subspace, Bochner integral averaging),
and the implicit function theorem on this Banach space gives the equilibrium.

## Main results

* `contDiff_codRestrict` (`Cᵏ` maps into a closed subspace), `isClosed_adSub`, `AvgL`, `NmS`,
  `Phi`, `contDiff_Phi`, `Phi_eq_zero_iff`, `linOp_apply` (the linearised operator in
  coordinates).
* `exists_smooth_solution` (**existence, local uniqueness, `Cᵏ` in `(y_{−1}, s₀, σ)`** for any
  Markov chain of regimes and bounded-support laws), `markov` (the solution is a time-invariant
  policy function of the state), `ift_identity`.
* `injective_ABC_of_isInvertible`: determinacy forces `A + B + C` injective (tent processes).
* i.i.d. laws: `markovU`, `markov_derivU`, `root_identity_iid`, `first_order_lag_iid`,
  `certainty_equivalence_iid` (`g_σ = 0` for ANY mean-zero bounded-support law),
  `second_order_sigma_iid` (the `σ²` equation with the variance `E[clip(ε)²]`),
  `integral_quad_clip`.
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaMeasure

open Filter Topology MeasureTheory
open scoped ContDiff
open SmoothInSigmaCE (tent tent_zero tent_self abs_tent_le abs_tent_succ_sub)
open SmoothInSigma (Bd mkBd mkBd_apply norm_apply_le norm_le_of_forall nem nem_apply mult
  mult_apply contDiff_nem hasFDerivAt_nem constBd constBd_apply evalL evalL_apply pbar zbar)

/-! ## Smooth maps into a closed subspace -/

/-- Woodford (2003), App. A.3, p. 632 (a functional-analytic tool): if `F` is differentiable at
`x` and takes values in a closed subspace `S`, so does its derivative. -/
theorem fderiv_mem_of_closed {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {S : Submodule ℝ B} (hS : IsClosed (S : Set B))
    {F : E → B} {F' : E →L[ℝ] B} {x : E} (hF : HasFDerivAt F F' x) (hmem : ∀ y, F y ∈ S)
    (v : E) : F' v ∈ S := by
  have h := hF.lim v (c := fun n : ℕ => (n : ℝ)) (l := atTop)
    (by simpa using tendsto_natCast_atTop_atTop (R := ℝ))
  exact hS.mem_of_tendsto h (Eventually.of_forall fun n =>
    S.smul_mem _ (S.sub_mem (hmem _) (hmem _)))

/-- Woodford (2003), App. A.3: the derivative of a map into a closed subspace, restricted. -/
theorem hasFDerivAt_codRestrict {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {S : Submodule ℝ B} (hS : IsClosed (S : Set B))
    {F : E → B} {F' : E →L[ℝ] B} {x : E} (hF : HasFDerivAt F F' x) (hmem : ∀ y, F y ∈ S) :
    HasFDerivAt (fun y => (⟨F y, hmem y⟩ : S))
      (F'.codRestrict S (fderiv_mem_of_closed hS hF hmem)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hF ⊢
  refine Asymptotics.IsLittleO.of_norm_left (hF.norm_left.congr_left fun h => ?_)
  rfl

/-- Woodford (2003), App. A.3: the closed subspace of linear maps with values in `S`. -/
def clmInto {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup B]
    [NormedSpace ℝ B] (S : Submodule ℝ B) : Submodule ℝ (E →L[ℝ] B) where
  carrier := {L | ∀ v, L v ∈ S}
  add_mem' := fun ha hb v => S.add_mem (ha v) (hb v)
  zero_mem' := fun _ => S.zero_mem
  smul_mem' := fun c _ ha v => S.smul_mem c (ha v)

/-- Woodford (2003), App. A.3: `clmInto S` is closed when `S` is. -/
theorem isClosed_clmInto {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] {S : Submodule ℝ B} (hS : IsClosed (S : Set B)) :
    IsClosed ((clmInto (E := E) S : Submodule ℝ (E →L[ℝ] B)) : Set (E →L[ℝ] B)) := by
  have : ((clmInto (E := E) S : Submodule ℝ (E →L[ℝ] B)) : Set (E →L[ℝ] B)) =
      ⋂ v : E, (fun L : E →L[ℝ] B => L v) ⁻¹' (S : Set B) := by
    ext L
    simp [clmInto]
  rw [this]
  exact isClosed_iInter fun v => hS.preimage (ContinuousLinearMap.apply ℝ B v).continuous

/-- Woodford (2003), App. A.3: restricting the codomain of a linear map in `clmInto S`, as a
bounded linear map. -/
noncomputable def codRestrictL {E B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (S : Submodule ℝ B) :
    clmInto (E := E) S →L[ℝ] (E →L[ℝ] S) :=
  LinearMap.mkContinuous
    { toFun := fun L : clmInto (E := E) S => (L : E →L[ℝ] B).codRestrict S L.prop
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun L => by
      rw [one_mul]
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
      exact (L : E →L[ℝ] B).le_opNorm v)

/-- Woodford (2003), App. A.3 (**a `Cᵏ` map into a closed subspace is `Cᵏ` as a map into the
subspace**), by induction on `k` through the derivative. -/
theorem contDiff_codRestrict {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (k : ℕ) {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] {S : Submodule ℝ B}
      (_hS : IsClosed (S : Set B)) {F : E → B} (_hF : ContDiff ℝ k F) (hmem : ∀ x, F x ∈ S),
      ContDiff ℝ k (fun x => (⟨F x, hmem x⟩ : S))
  | 0, _, _, _, _, _, F, hF, hmem => contDiff_zero.2 (hF.continuous.subtype_mk hmem)
  | k + 1, B, _, _, S, hS, F, hF, hmem => by
    have h1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hd : ∀ x, HasFDerivAt F (fderiv ℝ F x) x := fun x =>
      (h1.differentiable one_ne_zero x).hasFDerivAt
    have hm' : ∀ x, fderiv ℝ F x ∈ clmInto (E := E) S := fun x v =>
      fderiv_mem_of_closed hS (hd x) hmem v
    have hk : ContDiff ℝ k (fderiv ℝ F) := hF.fderiv_right (by push_cast; exact le_rfl)
    have hIH := contDiff_codRestrict k (isClosed_clmInto (E := E) hS) hk hm'
    have hder : fderiv ℝ (fun x => (⟨F x, hmem x⟩ : S)) =
        fun x => codRestrictL (E := E) S ⟨fderiv ℝ F x, hm' x⟩ :=
      funext fun x => by rw [(hasFDerivAt_codRestrict hS (hd x) hmem).fderiv]; rfl
    have key : ContDiff ℝ ((k : ℕ∞ω) + 1) (fun x => (⟨F x, hmem x⟩ : S)) := by
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hasFDerivAt_codRestrict hS (hd x) hmem).differentiableAt,
        fun h => by simp at h, ?_⟩
      rw [hder]
      exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (k : ℕ∞ω)) (E := clmInto (E := E) S)
        (F := E →L[ℝ] S) (codRestrictL (E := E) S)).comp hIH
    exact_mod_cast key


/-! ## Histories and the Banach space of adapted processes

A history `s : ℕ → R × ℝ` lists (regime, shock) pairs, newest first; at date `t` only the first
`t` pairs and the regime of entry `t` (the initial regime) matter. A process is a bounded family
`u (t, s)`, Borel measurable in the history at each date and depending only on the date-`t`
history ("finite memory"): these are exactly the bounded adapted processes, represented as
functions of the history. -/

/-- Woodford (2003), App. E.2, p. 695: histories of (regime, shock) pairs, newest first. -/
abbrev Hist (R : Type) : Type := ℕ → R × ℝ

variable {R : Type}

/-- Woodford (2003), App. E.2: the successor history after the new pair `a`. -/
def consH (a : R × ℝ) (s : Hist R) : Hist R := fun i => if i = 0 then a else s (i - 1)

/-- Woodford (2003), App. E.2: the predecessor history. -/
def tailH (s : Hist R) : Hist R := fun i => s (i + 1)

/-- Woodford (2003), App. E.2: `consH` at the newest entry. -/
@[simp] theorem consH_zero (a : R × ℝ) (s : Hist R) : consH a s 0 = a := rfl

/-- Woodford (2003), App. E.2: `consH` at older entries. -/
@[simp] theorem consH_succ (a : R × ℝ) (s : Hist R) (i : ℕ) : consH a s (i + 1) = s i := rfl

/-- Woodford (2003), App. E.2: the predecessor of a successor. -/
@[simp] theorem tailH_consH (a : R × ℝ) (s : Hist R) : tailH (consH a s) = s := rfl

/-- Woodford (2003), App. E.2 (the subtree below a node): the history of the node `(m + t + 1)`
reached from the date-`(t + 1)` history `s` along the `m` further pairs of `s''`, with the
current regime at the junction replaced by the subtree's root regime `(s'' m).1`. -/
def splice (m : ℕ) (s'' s : Hist R) : Hist R := fun i =>
  if i < m then s'' i else if i = m then ((s'' m).1, (s 0).2) else s (i - m)

/-- Woodford (2003), App. E.2: appending a pair commutes with splicing. -/
theorem consH_splice (a : R × ℝ) (m : ℕ) (s'' s : Hist R) :
    consH a (splice m s'' s) = splice (m + 1) (consH a s'') s := by
  funext i
  cases i with
  | zero => simp [consH, splice]
  | succ i =>
    simp only [consH, splice, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    split_ifs <;> first | rfl | (congr 1; omega)

/-- Woodford (2003), App. E.2: the predecessor of a spliced history. -/
theorem tailH_splice (m : ℕ) (s'' s : Hist R) :
    tailH (splice (m + 1) s'' s) = splice m (tailH s'') s := by
  funext i
  simp only [tailH, splice, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
  split_ifs <;> first | rfl | (congr 1; omega)

/-- Woodford (2003), App. E.2: splicing at the junction keeps the older history. -/
theorem tailH_splice_zero (s'' s : Hist R) : tailH (splice 0 s'' s) = tailH s := by
  funext i
  simp [tailH, splice]

/-- Woodford (2003), App. E.2: the newest pair of a spliced history. -/
theorem splice_zero_apply (m : ℕ) (s'' s : Hist R) :
    splice m s'' s 0 = if 0 < m then s'' 0 else ((s'' 0).1, (s 0).2) := by
  cases m <;> simp [splice]

/-- Woodford (2003), App. E.2: splicing the node's own regime at the junction gives the node. -/
theorem splice_zero_self (s : Hist R) (z : ℝ) :
    splice 0 (fun _ => ((s 0).1, z)) s = s := by
  funext i
  cases i <;> simp [splice]

/-- Woodford (2003), App. E.2: splicing is measurable in the subtree history. -/
theorem measurable_splice [MeasurableSpace R] (m : ℕ) (s : Hist R) :
    Measurable (fun s'' : Hist R => splice m s'' s) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [splice]
  split_ifs
  · exact measurable_pi_apply i
  · exact (measurable_fst.comp (measurable_pi_apply m)).prodMk measurable_const
  · exact measurable_const

/-- Woodford (2003), App. E.2, p. 695 (finite memory): `u (t, s)` depends only on the first `t`
pairs of `s` and on the regime of entry `t`. -/
def FinMem {V : Type} (u : ℕ × Hist R → V) : Prop :=
  ∀ t s s', (∀ i < t, s i = s' i) → (s t).1 = (s' t).1 → u (t, s) = u (t, s')

variable [MeasurableSpace R]

/-- Woodford (2003), App. E.2, p. 695 (**the bounded adapted processes**): bounded families,
measurable in the history at each date, with finite memory. -/
def adSub (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Submodule ℝ (Bd (ℕ × Hist R) V) where
  carrier := {u | (∀ t, StronglyMeasurable fun s => u (t, s)) ∧ FinMem (fun n => u n)}
  add_mem' := fun {a b} ha hb => ⟨fun t => by
      rw [lp.coeFn_add]
      exact (ha.1 t).add (hb.1 t),
    fun t s s' h1 h2 => by
      simp only [lp.coeFn_add, Pi.add_apply]
      exact congrArg₂ (· + ·) (ha.2 t s s' h1 h2) (hb.2 t s s' h1 h2)⟩
  zero_mem' := ⟨fun t => by simpa using stronglyMeasurable_const, fun t s s' _ _ => rfl⟩
  smul_mem' := fun c u hu => ⟨fun t => by
      rw [lp.coeFn_smul]
      exact (hu.1 t).const_smul c,
    fun t s s' h1 h2 => by
      simp only [lp.coeFn_smul, Pi.smul_apply]
      exact congrArg (c • ·) (hu.2 t s s' h1 h2)⟩

/-- Woodford (2003), App. E.2: the adapted processes form a closed subspace (measurability and
finite memory pass to uniform limits). -/
theorem isClosed_adSub (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    IsClosed ((adSub (R := R) V : Submodule ℝ (Bd (ℕ × Hist R) V)) : Set (Bd (ℕ × Hist R) V)) := by
  have hM : IsClosed {u : Bd (ℕ × Hist R) V | ∀ t, StronglyMeasurable fun s => u (t, s)} := by
    refine IsSeqClosed.isClosed fun {un u} hun hlim => fun t => ?_
    refine stronglyMeasurable_of_tendsto atTop (fun n => hun n t) ?_
    refine tendsto_pi_nhds.2 fun s => ?_
    exact ((evalL V (t, s)).continuous.tendsto u).comp hlim
  have hF : IsClosed {u : Bd (ℕ × Hist R) V | FinMem (fun n => u n)} := by
    have : {u : Bd (ℕ × Hist R) V | FinMem (fun n => u n)} =
        ⋂ (t : ℕ) (s : Hist R) (s' : Hist R) (_ : ∀ i < t, s i = s' i) (_ : (s t).1 = (s' t).1),
          {u | u (t, s) = u (t, s')} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, FinMem]
    rw [this]
    exact isClosed_iInter fun t => isClosed_iInter fun s => isClosed_iInter fun s' =>
      isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_eq (evalL V (t, s)).continuous (evalL V (t, s')).continuous
  exact hM.inter hF

/-- Woodford (2003), App. E.2: the predecessor map is measurable. -/
theorem measurable_tailH : Measurable (tailH : Hist R → Hist R) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)

/-- Woodford (2003), App. E.2: appending a new pair is jointly measurable. -/
theorem measurable_consH : Measurable (fun q : Hist R × (R × ℝ) => consH q.2 q.1) := by
  refine measurable_pi_iff.mpr fun i => ?_
  cases i with
  | zero => exact measurable_snd
  | succ i => exact (measurable_pi_apply i).comp measurable_fst

/-- Woodford (2003), App. E.2: the shock clipped to `[−B, B]`, `max(−B, min(B, e))` (the
identity on a support inside `[−B, B]`). -/
def clipB (B e : ℝ) : ℝ := max (-B) (min B e)

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `|clip(e)| ≤ |B|`. -/
theorem abs_clipB_le (B e : ℝ) : |clipB B e| ≤ |B| := by
  rw [clipB, abs_le]
  constructor
  · exact (neg_le_neg (le_abs_self B)).trans (le_max_left _ _)
  · exact max_le ((neg_le_abs B).trans le_rfl |>.trans' (by linarith [neg_abs_le B]))
      ((min_le_left _ _).trans (le_abs_self B))

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: clipping is continuous. -/
theorem continuous_clipB (B : ℝ) : Continuous (clipB B) :=
  continuous_const.max (continuous_const.min continuous_id)

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: clipping is the identity on `[−B, B]`. -/
theorem clipB_of_abs_le {B e : ℝ} (he : |e| ≤ B) : clipB B e = e := by
  rw [clipB, min_eq_right (le_abs_self e |>.trans he), max_eq_right (by linarith [neg_abs_le e])]

/-! ## The model with general (Markov-switching) shock laws -/

variable (R) (Y Z : Type)

/-- Woodford (2003), App. E.2, p. 695, and the perturbation method: the primitives of a
stochastic rational-expectations model `E_t f(y_{t+1}, y_t, y_{t−1}, σε_t, σε_{t+1}) = 0` with
shocks of ARBITRARY bounded-support laws: the next regime is drawn from the Markov matrix
`trans` given the current regime, and the next shock from `law` of the new regime (a single
regime is the i.i.d. case; Dirac laws give finitely many shock values). The current shock enters
`f`, so nonlinear exogenous laws `x_t = h(x_{t−1}, σε_t)` are components of the system. -/
structure MModel where
  /-- The period conditions `f(y_{t+1}, y_t, y_{t−1}, e_t, e_{t+1})`. -/
  f : Y × Y × Y × ℝ × ℝ → Z
  /-- The regime transition probabilities. -/
  trans : R → R → ℝ
  /-- The law of the shock in each regime. -/
  law : R → ProbabilityMeasure ℝ
  /-- The clipping bound `B` (a bound on the shock supports). -/
  bound : ℝ

variable {R Y Z}

namespace MModel

variable (M : MModel R Y Z)

/-- Woodford (2003), App. E.2: the standing assumptions, a stochastic transition matrix. -/
structure Std [Fintype R] where
  /-- Probabilities are nonnegative. -/
  trans_nonneg : ∀ r r', 0 ≤ M.trans r r'
  /-- Rows sum to one. -/
  trans_sum : ∀ r, ∑ r', M.trans r r' = 1


variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the predecessor value `y_{t−1}`, the given `y_{−1}` at date `0`;
parameters `p = (y_{−1}, s₀, σ)`. -/
def lagF (p : Y × ℝ × ℝ) (u : ℕ × Hist R → Y) : ℕ × Hist R → Y
  | (0, _) => p.1
  | (t + 1, s) => u (t, tailH s)

omit [MeasurableSpace R] [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: the current scaled shock, `s₀` at date `0` and `σ clip(ε_t)`
later. -/
def enowF (p : Y × ℝ × ℝ) : ℕ × Hist R → ℝ
  | (0, _) => p.2.1
  | (_ + 1, s) => p.2.2 * clipB M.bound (s 0).2

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2, p. 695: the argument of `f` at the node `(t + 1, s)`, i.e. on the
branch from `(t, tailH s)` to `(t + 1, s)`: `(y_{t+1}, y_t, y_{t−1}, e_t, σ clip(ε_{t+1}))`
(and `0` at date `0`, which is no successor). -/
def wfun (p : Y × ℝ × ℝ) (u : ℕ × Hist R → Y) : ℕ × Hist R → Y × Y × Y × ℝ × ℝ
  | (0, _) => 0
  | (t + 1, s) => (u (t + 1, s), u (t, tailH s), lagF p u (t, tailH s), M.enowF p (t, tailH s),
      p.2.2 * clipB M.bound (s 0).2)

omit [MeasurableSpace R] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: `lagF` is linear. -/
theorem lagF_add (p p' : Y × ℝ × ℝ) (u u' : ℕ × Hist R → Y) (n : ℕ × Hist R) :
    lagF (p + p') (u + u') n = lagF p u n + lagF p' u' n := by
  rcases n with ⟨_ | t, s⟩ <;> rfl

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `lagF` is homogeneous. -/
theorem lagF_smul (c : ℝ) (p : Y × ℝ × ℝ) (u : ℕ × Hist R → Y) (n : ℕ × Hist R) :
    lagF (c • p) (c • u) n = c • lagF p u n := by
  rcases n with ⟨_ | t, s⟩ <;> rfl

omit [MeasurableSpace R] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: `enowF` is linear. -/
theorem enowF_add (p p' : Y × ℝ × ℝ) (n : ℕ × Hist R) :
    M.enowF (p + p') n = M.enowF p n + M.enowF p' n := by
  rcases n with ⟨_ | t, s⟩
  · rfl
  · simp only [enowF, Prod.snd_add]
    ring

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `enowF` is homogeneous. -/
theorem enowF_smul (c : ℝ) (p : Y × ℝ × ℝ) (n : ℕ × Hist R) :
    M.enowF (c • p) n = c * M.enowF p n := by
  rcases n with ⟨_ | t, s⟩
  · rfl
  · simp only [enowF, Prod.smul_snd, smul_eq_mul]
    ring

omit [MeasurableSpace R] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: `wfun` is linear in `(p, u)`. -/
theorem wfun_add (p p' : Y × ℝ × ℝ) (u u' : ℕ × Hist R → Y) (n : ℕ × Hist R) :
    M.wfun (p + p') (u + u') n = M.wfun p u n + M.wfun p' u' n := by
  rcases n with ⟨_ | t, s⟩
  · simp [wfun]
  · simp only [wfun, Pi.add_apply, lagF_add, enowF_add, Prod.snd_add, Prod.mk_add_mk, add_mul]

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: `wfun` is homogeneous in `(p, u)`. -/
theorem wfun_smul (c : ℝ) (p : Y × ℝ × ℝ) (u : ℕ × Hist R → Y) (n : ℕ × Hist R) :
    M.wfun (c • p) (c • u) n = c • M.wfun p u n := by
  rcases n with ⟨_ | t, s⟩
  · simp [wfun]
  · simp only [wfun, Pi.smul_apply, lagF_smul, enowF_smul, Prod.smul_snd, Prod.smul_mk,
      smul_eq_mul, mul_assoc]

omit [MeasurableSpace R] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: the arguments of `f` are bounded uniformly over the tree,
`‖w_n‖ ≤ (1 + |B|) ‖(p, u)‖`. -/
theorem norm_wfun_le (p : Y × ℝ × ℝ) (u : Bd (ℕ × Hist R) Y) (n : ℕ × Hist R) :
    ‖M.wfun p u n‖ ≤ (1 + |M.bound|) * ‖((p, u) : (Y × ℝ × ℝ) × Bd (ℕ × Hist R) Y)‖ := by
  set q : (Y × ℝ × ℝ) × Bd (ℕ × Hist R) Y := (p, u) with hq
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hu : ‖u‖ ≤ ‖q‖ := norm_snd_le q
  have hp : ‖p‖ ≤ ‖q‖ := norm_fst_le q
  have hp1 : ‖p.1‖ ≤ ‖q‖ := (norm_fst_le p).trans hp
  have hp2 : |p.2.1| ≤ ‖q‖ := by
    rw [← Real.norm_eq_abs]; exact ((norm_fst_le p.2).trans (norm_snd_le p)).trans hp
  have hp3 : |p.2.2| ≤ ‖q‖ := by
    rw [← Real.norm_eq_abs]; exact ((norm_snd_le p.2).trans (norm_snd_le p)).trans hp
  have hC : ‖q‖ ≤ (1 + |M.bound|) * ‖q‖ := by nlinarith [abs_nonneg M.bound]
  have hcl : ∀ e : ℝ, ‖p.2.2 * clipB M.bound e‖ ≤ (1 + |M.bound|) * ‖q‖ := fun e => by
    rw [Real.norm_eq_abs, abs_mul]
    calc |p.2.2| * |clipB M.bound e| ≤ ‖q‖ * |M.bound| :=
          mul_le_mul hp3 (abs_clipB_le _ _) (abs_nonneg _) hq0
      _ ≤ (1 + |M.bound|) * ‖q‖ := by nlinarith [abs_nonneg M.bound]
  have hun : ∀ m, ‖u m‖ ≤ (1 + |M.bound|) * ‖q‖ := fun m => ((norm_apply_le u m).trans hu).trans hC
  rcases n with ⟨_ | t, s⟩
  · simp only [wfun, norm_zero]
    positivity
  · have hl : ‖lagF p u (t, tailH s)‖ ≤ (1 + |M.bound|) * ‖q‖ := by
      cases t with
      | zero => exact hp1.trans hC
      | succ t => exact hun _
    have he : ‖M.enowF p (t, tailH s)‖ ≤ (1 + |M.bound|) * ‖q‖ := by
      cases t with
      | zero => rw [Real.norm_eq_abs]; exact hp2.trans hC
      | succ t => exact hcl _
    simp only [wfun, norm_prod_le_iff]
    exact ⟨hun _, hun _, hl, he, hcl _⟩


omit [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: the arguments of `f` form an adapted family (measurable, finite
memory) when the candidate solution does. -/
theorem wfun_adapted (p : Y × ℝ × ℝ) {u : ℕ × Hist R → Y}
    (hum : ∀ t, StronglyMeasurable fun s => u (t, s)) (huf : FinMem u) :
    (∀ t, StronglyMeasurable fun s => M.wfun p u (t, s)) ∧ FinMem (M.wfun p u) := by
  have hcl : StronglyMeasurable fun s : Hist R => p.2.2 * clipB M.bound (s 0).2 :=
    (measurable_const.mul ((continuous_clipB M.bound).measurable.comp
      (measurable_snd.comp (measurable_pi_apply 0)))).stronglyMeasurable
  have htl : ∀ t, StronglyMeasurable fun s : Hist R => u (t, tailH s) := fun t =>
    (hum t).comp_measurable measurable_tailH
  refine ⟨fun t => ?_, fun t s s' h1 h2 => ?_⟩
  · cases t with
    | zero => exact stronglyMeasurable_const
    | succ t =>
      have hl : StronglyMeasurable fun s : Hist R => lagF p u (t, tailH s) := by
        cases t with
        | zero => exact stronglyMeasurable_const
        | succ t => exact (htl t).comp_measurable measurable_tailH
      have he : StronglyMeasurable fun s : Hist R => M.enowF p (t, tailH s) := by
        cases t with
        | zero => exact stronglyMeasurable_const
        | succ t => exact hcl.comp_measurable measurable_tailH
      exact (hum (t + 1)).prodMk ((htl t).prodMk (hl.prodMk (he.prodMk hcl)))
  · cases t with
    | zero => rfl
    | succ t =>
      have e1 : u (t + 1, s) = u (t + 1, s') := huf (t + 1) s s' h1 h2
      have e2 : u (t, tailH s) = u (t, tailH s') :=
        huf t (tailH s) (tailH s') (fun i hi => h1 (i + 1) (by omega)) h2
      have e3 : lagF p u (t, tailH s) = lagF p u (t, tailH s') := by
        cases t with
        | zero => rfl
        | succ t =>
          exact huf t (tailH (tailH s)) (tailH (tailH s')) (fun i hi => h1 (i + 2) (by omega)) h2
      have e4 : M.enowF p (t, tailH s) = M.enowF p (t, tailH s') := by
        cases t with
        | zero => rfl
        | succ t =>
          simp only [enowF, tailH]
          rw [h1 1 (by omega)]
      have e5 : (s 0).2 = (s' 0).2 := by rw [h1 0 (by omega)]
      simp only [wfun]
      rw [e1, e2, e3, e4, e5]

/-- Woodford (2003), App. E.2, p. 695: the arguments of `f` as a bounded linear map from the
parameters and the candidate solution into the adapted families. -/
noncomputable def WmapL : (Y × ℝ × ℝ) × adSub (R := R) Y →L[ℝ]
    adSub (R := R) (Y × Y × Y × ℝ × ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun q => ⟨mkBd (M.wfun q.1 q.2) ⟨_, fun n => M.norm_wfun_le q.1 q.2 n⟩,
        M.wfun_adapted q.1 q.2.2.1 q.2.2.2⟩
      map_add' := fun q q' => by
        refine Subtype.ext (lp.ext (funext fun n => ?_))
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, lp.coeFn_add, mkBd_apply,
          Pi.add_apply]
        exact M.wfun_add _ _ _ _ n
      map_smul' := fun c q => by
        refine Subtype.ext (lp.ext (funext fun n => ?_))
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, lp.coeFn_smul, mkBd_apply,
          Pi.smul_apply, RingHom.id_apply]
        exact M.wfun_smul _ _ _ n }
    (1 + |M.bound|) (fun q => by
      refine norm_le_of_forall (by positivity) fun n => ?_
      exact M.norm_wfun_le q.1 q.2 n)

/-- Woodford (2003), App. E.2: members of `WmapL`. -/
@[simp] theorem WmapL_apply (q : (Y × ℝ × ℝ) × adSub (R := R) Y) (n : ℕ × Hist R) :
    ((M.WmapL q : adSub (R := R) (Y × Y × Y × ℝ × ℝ)) : Bd (ℕ × Hist R) _) n =
      M.wfun q.1 q.2 n :=
  rfl


variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: along a branch, an adapted family is an integrable function of the
next shock. -/
theorem integrable_branch {g : Bd (ℕ × Hist R) Z} (hg : g ∈ adSub (R := R) Z) (t : ℕ)
    (s : Hist R) (r' : R) :
    Integrable (fun e => g (t + 1, consH (r', e) s)) (M.law r' : Measure ℝ) := by
  have hm : StronglyMeasurable fun e : ℝ => g (t + 1, consH (r', e) s) :=
    (hg.1 (t + 1)).comp_measurable (measurable_consH.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
  exact Integrable.of_bound hm.aestronglyMeasurable ‖g‖ (Eventually.of_forall fun e =>
    norm_apply_le g _)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2, p. 695 (**the conditional expectation on the event tree**):
`(E g)(t, s) = ∑_{r'} P(r_t, r') ∫ g(t + 1, (r', e) :: s) dν_{r'}(e)`. -/
noncomputable def avgFun [Fintype R] (g : ℕ × Hist R → Z) : ℕ × Hist R → Z := fun n =>
  ∑ r', M.trans (n.2 0).1 r' • ∫ e, g (n.1 + 1, consH (r', e) n.2) ∂(M.law r' : Measure ℝ)

variable [Fintype R]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace R] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the conditional expectation does not increase the sup norm. -/
theorem norm_avgFun_le (hM : M.Std) (g : Bd (ℕ × Hist R) Z) (n : ℕ × Hist R) :
    ‖M.avgFun g n‖ ≤ ‖g‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r', ‖M.trans (n.2 0).1 r' • ∫ e, g (n.1 + 1, consH (r', e) n.2) ∂(M.law r' : Measure ℝ)‖
      ≤ ∑ r', M.trans (n.2 0).1 r' * ‖g‖ := Finset.sum_le_sum fun r' _ => by
        rw [norm_smul, Real.norm_of_nonneg (hM.trans_nonneg _ _)]
        refine mul_le_mul_of_nonneg_left ?_ (hM.trans_nonneg _ _)
        have := norm_integral_le_of_norm_le_const (μ := (M.law r' : Measure ℝ))
          (f := fun e => g (n.1 + 1, consH (r', e) n.2)) (C := ‖g‖)
          (Eventually.of_forall fun e => norm_apply_le g _)
        simpa using this
    _ = ‖g‖ := by rw [← Finset.sum_mul, hM.trans_sum, one_mul]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the conditional expectation of an adapted family is adapted. -/
theorem avgFun_adapted [MeasurableSingletonClass R] {g : Bd (ℕ × Hist R) Z}
    (hg : g ∈ adSub (R := R) Z) :
    (∀ t, StronglyMeasurable fun s => M.avgFun g (t, s)) ∧ FinMem (M.avgFun g) := by
  refine ⟨fun t => ?_, fun t s s' h1 h2 => ?_⟩
  · refine Finset.stronglyMeasurable_fun_sum (f := fun r' (s : Hist R) => M.trans (s 0).1 r' •
      ∫ e, g (t + 1, consH (r', e) s) ∂(M.law r' : Measure ℝ)) _ fun r' _ => ?_
    have hP : StronglyMeasurable fun s : Hist R => M.trans (s 0).1 r' :=
      ((measurable_of_countable (fun r => M.trans r r')).comp
        (measurable_fst.comp (measurable_pi_apply 0))).stronglyMeasurable
    have hI : StronglyMeasurable fun s : Hist R =>
        ∫ e, g (t + 1, consH (r', e) s) ∂(M.law r' : Measure ℝ) :=
      StronglyMeasurable.integral_prod_right' (f := fun q : Hist R × ℝ =>
        g (t + 1, consH (r', q.2) q.1))
        ((hg.1 (t + 1)).comp_measurable (measurable_consH.comp
          (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))))
    exact hP.smul hI
  · have h0 : (s 0).1 = (s' 0).1 := by
      cases t with
      | zero => exact h2
      | succ t => rw [h1 0 (by omega)]
    have hb : ∀ r' e, g (t + 1, consH (r', e) s) = g (t + 1, consH (r', e) s') := fun r' e =>
      hg.2 (t + 1) _ _ (fun i hi => by
        cases i with
        | zero => rfl
        | succ i => exact h1 i (by omega)) h2
    simp only [avgFun, h0, hb]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the conditional expectation is additive on adapted families. -/
theorem avgFun_add {g g' : Bd (ℕ × Hist R) Z} (hg : g ∈ adSub (R := R) Z)
    (hg' : g' ∈ adSub (R := R) Z) (n : ℕ × Hist R) :
    M.avgFun (⇑(g + g')) n = M.avgFun g n + M.avgFun g' n := by
  simp only [avgFun, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [← integral_add (M.integrable_branch hg _ _ _) (M.integrable_branch hg' _ _ _)]
  rfl

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace R] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the conditional expectation is homogeneous. -/
theorem avgFun_smul (c : ℝ) (g : Bd (ℕ × Hist R) Z) (n : ℕ × Hist R) :
    M.avgFun (⇑(c • g)) n = c • M.avgFun g n := by
  simp only [avgFun, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r' _ => ?_
  have : ∫ e, (⇑(c • g)) (n.1 + 1, consH (r', e) n.2) ∂(M.law r' : Measure ℝ) =
      c • ∫ e, g (n.1 + 1, consH (r', e) n.2) ∂(M.law r' : Measure ℝ) := by
    simp only [lp.coeFn_smul, Pi.smul_apply]
    exact integral_smul c _
  rw [this, smul_comm]

variable [MeasurableSingletonClass R]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2, p. 695: the conditional expectation as a bounded linear operator
(of norm at most one) on the adapted families. -/
noncomputable def AvgL (hM : M.Std) : adSub (R := R) Z →L[ℝ] adSub (R := R) Z :=
  LinearMap.mkContinuous
    { toFun := fun g => ⟨mkBd (M.avgFun g) ⟨‖g‖, M.norm_avgFun_le hM g⟩,
        M.avgFun_adapted g.2⟩
      map_add' := fun g g' => by
        refine Subtype.ext (lp.ext (funext fun n => ?_))
        simp only [Submodule.coe_add, lp.coeFn_add, mkBd_apply, Pi.add_apply]
        exact M.avgFun_add g.2 g'.2 n
      map_smul' := fun c g => by
        refine Subtype.ext (lp.ext (funext fun n => ?_))
        simp only [Submodule.coe_smul, lp.coeFn_smul, mkBd_apply, Pi.smul_apply,
          RingHom.id_apply]
        exact M.avgFun_smul c g n }
    1 (fun g => by
      rw [one_mul]
      exact norm_le_of_forall (norm_nonneg _) fun n => M.norm_avgFun_le hM g n)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: members of `AvgL`. -/
@[simp] theorem AvgL_apply (hM : M.Std) (g : adSub (R := R) Z) (n : ℕ × Hist R) :
    ((M.AvgL hM g : adSub (R := R) Z) : Bd (ℕ × Hist R) Z) n = M.avgFun g n :=
  rfl

variable [FiniteDimensional ℝ Y]

omit [Fintype R] [MeasurableSingletonClass R] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: `f` applied to an adapted family is adapted. -/
theorem nem_mem (hc : Continuous M.f) (w : adSub (R := R) (Y × Y × Y × ℝ × ℝ)) :
    nem M.f hc (w : Bd (ℕ × Hist R) _) ∈ adSub (R := R) Z :=
  ⟨fun t => hc.comp_stronglyMeasurable (w.2.1 t),
    fun t s s' h1 h2 => congrArg M.f (w.2.2 t s s' h1 h2)⟩

omit [Fintype R] [MeasurableSingletonClass R] in
/-- Woodford (2003), App. E.2, p. 695: the Nemytskii operator of `f` on adapted families. -/
noncomputable def NmS (hc : Continuous M.f) (w : adSub (R := R) (Y × Y × Y × ℝ × ℝ)) :
    adSub (R := R) Z :=
  ⟨nem M.f hc (w : Bd (ℕ × Hist R) _), M.nem_mem hc w⟩

omit [Fintype R] [MeasurableSingletonClass R] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695: the Nemytskii operator on adapted families is `Cᵏ`
(`contDiff_nem` and `contDiff_codRestrict`). -/
theorem contDiff_NmS {k : ℕ} (hf : ContDiff ℝ k M.f) :
    ContDiff ℝ k (M.NmS (R := R) hf.continuous) := by
  have hF : ContDiff ℝ k (fun w : adSub (R := R) (Y × Y × Y × ℝ × ℝ) =>
      nem M.f hf.continuous (w : Bd (ℕ × Hist R) _)) :=
    (contDiff_nem k M.f hf).comp (adSub (R := R) (Y × Y × Y × ℝ × ℝ)).subtypeL.contDiff
  exact contDiff_codRestrict k (isClosed_adSub Z) hF (fun w => M.nem_mem hf.continuous w)

/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium map**): parameters and an adapted
candidate solution to the adapted family of residuals
`(t, s) ↦ E[f(y_{t+1}, y_t, y_{t−1}, e_t, σ clip(ε_{t+1})) | history s]`. -/
noncomputable def Phi (hM : M.Std) (hc : Continuous M.f)
    (q : (Y × ℝ × ℝ) × adSub (R := R) Y) : adSub (R := R) Z :=
  M.AvgL hM (M.NmS hc (M.WmapL q))

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the equilibrium map is `Cᵏ` when `f` is. -/
theorem contDiff_Phi (hM : M.Std) {k : ℕ} (hf : ContDiff ℝ k M.f) :
    ContDiff ℝ k (M.Phi (R := R) hM hf.continuous) :=
  (M.AvgL hM).contDiff.comp ((M.contDiff_NmS hf).comp (M.WmapL (R := R)).contDiff)

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: members of the equilibrium map. -/
theorem Phi_apply (hM : M.Std) (hc : Continuous M.f) (q : (Y × ℝ × ℝ) × adSub (R := R) Y)
    (t : ℕ) (s : Hist R) :
    ((M.Phi hM hc q : adSub (R := R) Z) : Bd (ℕ × Hist R) Z) (t, s) =
      ∑ r', M.trans (s 0).1 r' • ∫ e, M.f ((q.2 : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s),
        (q.2 : Bd (ℕ × Hist R) Y) (t, s), lagF q.1 (q.2 : Bd (ℕ × Hist R) Y) (t, s),
        M.enowF q.1 (t, s), q.1.2.2 * clipB M.bound e) ∂(M.law r' : Measure ℝ) :=
  rfl

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [MeasurableSpace R] in
/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium conditions**): at every date and
history, `E[f(y_{t+1}, y_t, y_{t−1}, e_t, σ clip(ε_{t+1})) | s] = 0`, the expectation over the
next regime and shock. -/
def Solves (u : ℕ × Hist R → Y) (p : Y × ℝ × ℝ) : Prop :=
  ∀ t s, ∑ r', M.trans (s 0).1 r' • ∫ e, M.f (u (t + 1, consH (r', e) s), u (t, s),
    lagF p u (t, s), M.enowF p (t, s), p.2.2 * clipB M.bound e) ∂(M.law r' : Measure ℝ) = 0

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the zeros of the equilibrium map are the solutions. -/
theorem Phi_eq_zero_iff (hM : M.Std) (hc : Continuous M.f) (p : Y × ℝ × ℝ)
    (u : adSub (R := R) Y) : M.Phi hM hc (p, u) = 0 ↔ M.Solves u p := by
  constructor
  · intro h t s
    have := congrArg (fun w : adSub (R := R) Z => (w : Bd (ℕ × Hist R) Z) (t, s)) h
    simpa [Phi_apply] using this
  · intro h
    refine Subtype.ext (lp.ext (funext fun n => ?_))
    rcases n with ⟨t, s⟩
    rw [Phi_apply]
    exact h t s

/-! ### The steady state and the linearisation -/

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the constant process `ȳ` is adapted. -/
theorem constBd_mem (c : Y) : (constBd c : Bd (ℕ × Hist R) Y) ∈ adSub (R := R) Y :=
  ⟨fun _ => stronglyMeasurable_const, fun _ _ _ _ _ => rfl⟩

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [NormedSpace ℝ Y]
  [MeasurableSpace R] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: at the steady state `(p̄, ȳ)` every branch argument is `z̄`. -/
theorem wfun_bar (ybar : Y) (t : ℕ) (s : Hist R) :
    M.wfun (pbar ybar : Y × ℝ × ℝ) (constBd ybar : Bd (ℕ × Hist R) Y) (t + 1, s) = zbar ybar := by
  cases t <;> simp [wfun, lagF, enowF, pbar, zbar]

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the steady state solves the deterministic model,
`Φ(p̄, ȳ) = 0`. -/
theorem Phi_bar (hM : M.Std) (hc : Continuous M.f) {ybar : Y} (hss : M.f (zbar ybar) = 0) :
    M.Phi hM hc ((pbar ybar : Y × ℝ × ℝ), ⟨constBd ybar, constBd_mem ybar⟩) = 0 := by
  refine Subtype.ext (lp.ext (funext fun n => ?_))
  rcases n with ⟨t, s⟩
  rw [Phi_apply]
  have : ∀ (r' : R) (e : ℝ), M.f ((constBd ybar : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s),
      (constBd ybar : Bd (ℕ × Hist R) Y) (t, s),
      lagF (pbar ybar : Y × ℝ × ℝ) (constBd ybar : Bd (ℕ × Hist R) Y) (t, s),
      M.enowF (pbar ybar : Y × ℝ × ℝ) (t, s), (pbar ybar : Y × ℝ × ℝ).2.2 * clipB M.bound e) =
      0 := fun r' e => by
    have := M.wfun_bar ybar t (consH (r', e) s)
    simp only [wfun, tailH_consH, consH_zero] at this
    rw [this, hss]
  simp only [this, integral_zero, smul_zero, Finset.sum_const_zero]
  rfl

/-- Woodford (2003), App. E.2: `A = ∂f/∂y_{t+1}` at the steady state. -/
noncomputable def dA (ybar : Y) : Y →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp (ContinuousLinearMap.inl ℝ Y (Y × Y × ℝ × ℝ))

/-- Woodford (2003), App. E.2: `B = ∂f/∂y_t` at the steady state. -/
noncomputable def dB (ybar : Y) : Y →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × ℝ × ℝ)).comp
    (ContinuousLinearMap.inl ℝ Y (Y × ℝ × ℝ)))

/-- Woodford (2003), App. E.2: `C = ∂f/∂y_{t−1}` at the steady state. -/
noncomputable def dC (ybar : Y) : Y →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × ℝ × ℝ)).comp
    ((ContinuousLinearMap.inr ℝ Y (Y × ℝ × ℝ)).comp (ContinuousLinearMap.inl ℝ Y (ℝ × ℝ))))

/-- Woodford (2003), App. E.2: `f_{e_t}`, the derivative in the current shock. -/
noncomputable def dN (ybar : Y) : ℝ →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × ℝ × ℝ)).comp
    ((ContinuousLinearMap.inr ℝ Y (Y × ℝ × ℝ)).comp ((ContinuousLinearMap.inr ℝ Y (ℝ × ℝ)).comp
      (ContinuousLinearMap.inl ℝ ℝ ℝ))))

/-- Woodford (2003), App. E.2: `f_{e_{t+1}}`, the derivative in the next shock. -/
noncomputable def dE (ybar : Y) : ℝ →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × ℝ × ℝ)).comp
    ((ContinuousLinearMap.inr ℝ Y (Y × ℝ × ℝ)).comp ((ContinuousLinearMap.inr ℝ Y (ℝ × ℝ)).comp
      (ContinuousLinearMap.inr ℝ ℝ ℝ))))

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [MeasurableSpace R]
  [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: `Df(z̄)(a, b, c, n, e) = A a + B b + C c + f_n n + f_e e`. -/
theorem fderiv_f_apply (ybar : Y) (a b c : Y) (n e : ℝ) :
    fderiv ℝ M.f (zbar ybar) (a, b, c, n, e) =
      M.dA ybar a + M.dB ybar b + M.dC ybar c + M.dN ybar n + M.dE ybar e := by
  simp only [dA, dB, dC, dN, dE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the steady-state candidate, the constant process `ȳ`. -/
noncomputable def ubar (ybar : Y) : adSub (R := R) Y := ⟨constBd ybar, constBd_mem ybar⟩

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the space of adapted processes is complete. -/
theorem completeSpace_adSub (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [MeasurableSpace R] : CompleteSpace (adSub (R := R) V) := by
  have := isClosed_adSub (R := R) V
  exact IsClosed.completeSpace_coe

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695 (**the derivative of the equilibrium map at the steady
state**, in coordinates): in the direction `(v, h)`, at `(t, s)`,
`∑_{r'} P(r_t, r') ∫ Df(z̄)(w_{(v,h)}(t + 1, (r', e) :: s)) dν_{r'}(e)`. -/
theorem fderiv_Phi_apply (hM : M.Std) (hc : Continuous M.f) (hf : ContDiff ℝ 1 M.f) (ybar : Y)
    (q : (Y × ℝ × ℝ) × adSub (R := R) Y) (t : ℕ) (s : Hist R) :
    ((fderiv ℝ (M.Phi hM hc) ((pbar ybar : Y × ℝ × ℝ), ubar ybar) q : adSub (R := R) Z) :
      Bd (ℕ × Hist R) Z) (t, s) =
      ∑ r', M.trans (s 0).1 r' • ∫ e, fderiv ℝ M.f (zbar ybar)
        (M.wfun q.1 (q.2 : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s))
        ∂(M.law r' : Measure ℝ) := by
  set qb : (Y × ℝ × ℝ) × adSub (R := R) Y := ((pbar ybar : Y × ℝ × ℝ), ubar ybar) with hqb
  set wb := M.WmapL qb with hwb
  have hF : HasFDerivAt (fun w : adSub (R := R) (Y × Y × Y × ℝ × ℝ) =>
      nem M.f hf.continuous (w : Bd (ℕ × Hist R) _))
      ((mult Z (nem (fderiv ℝ M.f) (hf.continuous_fderiv one_ne_zero)
        (wb : Bd (ℕ × Hist R) _))).comp
        (adSub (R := R) (Y × Y × Y × ℝ × ℝ)).subtypeL) wb :=
    by
      have h1 := hasFDerivAt_nem (ν := ℕ × Hist R) hf (wb : Bd (ℕ × Hist R) _)
      exact h1.comp wb (adSub (R := R) (Y × Y × Y × ℝ × ℝ)).subtypeL.hasFDerivAt
  have hN := hasFDerivAt_codRestrict (isClosed_adSub Z) hF (fun w => M.nem_mem hf.continuous w)
  have hP : HasFDerivAt (M.Phi hM hc) ((M.AvgL hM).comp
      (((mult Z (nem (fderiv ℝ M.f) (hf.continuous_fderiv one_ne_zero)
        (wb : Bd (ℕ × Hist R) _))).comp
        (adSub (R := R) (Y × Y × Y × ℝ × ℝ)).subtypeL).codRestrict (adSub Z)
          (fderiv_mem_of_closed (isClosed_adSub Z) hF (fun w => M.nem_mem hf.continuous w)) |>.comp
        (M.WmapL (R := R)))) qb :=
    by
      have h2 := hN.comp qb (M.WmapL (R := R)).hasFDerivAt
      exact (M.AvgL hM).hasFDerivAt.comp qb h2
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.comp_apply, AvgL_apply, avgFun]
  refine Finset.sum_congr rfl fun r' _ => ?_
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  change fderiv ℝ M.f (M.wfun (pbar ybar : Y × ℝ × ℝ) (constBd ybar : Bd (ℕ × Hist R) Y)
    (t + 1, consH (r', e) s)) (M.wfun q.1 (q.2 : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s)) = _
  rw [M.wfun_bar ybar t]

/-- Woodford (2003), App. E.2, p. 695 (**the linearised operator**): the derivative of the
equilibrium map in the candidate solution at the steady state. -/
noncomputable def linOp (hM : M.Std) (hc : Continuous M.f) (ybar : Y) :=
  (fderiv ℝ (M.Phi hM hc) ((pbar ybar : Y × ℝ × ℝ), ubar ybar)).comp
    (ContinuousLinearMap.inr ℝ (Y × ℝ × ℝ) (adSub (R := R) Y))

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695 (**the linearised model in coordinates**):
`(L h)(t, s) = ∑_{r'} P(r_t, r') ∫ [A h(t + 1, (r', e) :: s) + B h(t, s) + C h_{t−1}] dν_{r'}`,
with `h_{−1} = 0`. -/
theorem linOp_apply (hM : M.Std) (hc : Continuous M.f) (hf : ContDiff ℝ 1 M.f) (ybar : Y)
    (h : adSub (R := R) Y) (t : ℕ) (s : Hist R) :
    ((M.linOp hM hc ybar h : adSub (R := R) Z) : Bd (ℕ × Hist R) Z) (t, s) =
      ∑ r', M.trans (s 0).1 r' • ∫ e,
        (M.dA ybar ((h : Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s)) +
        M.dB ybar ((h : Bd (ℕ × Hist R) Y) (t, s)) +
        M.dC ybar (lagF 0 (h : Bd (ℕ × Hist R) Y) (t, s))) ∂(M.law r' : Measure ℝ) := by
  rw [linOp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    M.fderiv_Phi_apply hM hc hf ybar]
  refine Finset.sum_congr rfl fun r' _ => ?_
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  have hn : M.enowF (0 : Y × ℝ × ℝ) (t, s) = 0 := by
    cases t <;> simp [enowF]
  simp only [wfun, tailH_consH, consH_zero, Prod.snd_zero, zero_mul, fderiv_f_apply, hn,
    map_zero, add_zero]

variable (ybar : Y) (ψ : Y × ℝ × ℝ → adSub (R := R) Y) in
/-- Woodford (2003), App. E.2, p. 695 (**a local equilibrium**): `ψ(p)` is an adapted bounded
solution for parameters `p = (y_{−1}, s₀, σ)` near `p̄ = (ȳ, 0, 0)`, equal to `ȳ` at `p̄`,
continuous there, and the only adapted solution near `ȳ` (sup norm) for parameters near `p̄`. -/
structure LocalSol where
  /-- `ψ(p̄) = ȳ`. -/
  base : ψ (pbar ybar) = ubar ybar
  /-- `ψ` is continuous at `p̄`. -/
  cont : ContinuousAt ψ (pbar ybar)
  /-- `ψ(p)` solves the model near `p̄`. -/
  solves : ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ), M.Solves (ψ p : Bd (ℕ × Hist R) Y) p
  /-- Local uniqueness among adapted processes. -/
  unique : ∃ δ > 0, ∀ (p : Y × ℝ × ℝ) (u : adSub (R := R) Y), dist p (pbar ybar) < δ →
    dist u (ubar ybar) < δ → M.Solves (u : Bd (ℕ × Hist R) Y) p → ψ p = u

/-- Woodford (2003), App. E.2, p. 695, and the perturbation method, for GENERAL bounded-support
shock laws (**existence, local uniqueness and `Cᵏ` dependence on `(y_{−1}, s₀, σ)`**): if `f` is
`Cᵏ` (`k ≥ 1`), `f(z̄) = 0`, and the linearised operator is invertible on the adapted processes
(determinacy), there is a local equilibrium `ψ`, `Cᵏ` at `p̄` as a map into the bounded adapted
processes. -/
theorem exists_smooth_solution [CompleteSpace Y] (hM : M.Std) {k : ℕ}
    (hk : 1 ≤ k) (hf : ContDiff ℝ k M.f) {ybar : Y} (hss : M.f (zbar ybar) = 0)
    (hdet : (M.linOp hM hf.continuous ybar).IsInvertible) :
    ∃ ψ : Y × ℝ × ℝ → adSub (R := R) Y, M.LocalSol ybar ψ ∧ ContDiffAt ℝ k ψ (pbar ybar) := by
  have := completeSpace_adSub (R := R) Y
  have := completeSpace_adSub (R := R) Z
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have cdf : ContDiffAt ℝ k (M.Phi hM hf.continuous) ((pbar ybar : Y × ℝ × ℝ), ubar ybar) :=
    (M.contDiff_Phi hM hf).contDiffAt
  have h0 : M.Phi hM hf.continuous ((pbar ybar : Y × ℝ × ℝ), ubar ybar) = 0 :=
    M.Phi_bar hM hf.continuous hss
  refine ⟨cdf.implicitFunction hk0 hdet, ⟨cdf.implicitFunction_apply_self hk0 hdet,
    (cdf.contDiffAt_implicitFunction hk0 hdet).continuousAt, ?_, ?_⟩,
    cdf.contDiffAt_implicitFunction hk0 hdet⟩
  · filter_upwards [cdf.eventually_apply_implicitFunction hk0 hdet] with p hp
    rw [h0] at hp
    exact (M.Phi_eq_zero_iff hM hf.continuous p _).1 hp
  · obtain ⟨δ, hδ, h⟩ :=
      Metric.eventually_nhds_iff.1 (cdf.eventually_apply_eq_iff_implicitFunction hk0 hdet)
    refine ⟨δ, hδ, fun p u hp hu hs => ?_⟩
    have hd : dist (p, u) ((pbar ybar : Y × ℝ × ℝ), ubar ybar) < δ := by
      rw [Prod.dist_eq]
      exact max_lt hp hu
    exact (h hd).1 (by rw [h0]; exact (M.Phi_eq_zero_iff hM hf.continuous p u).2 hs)

/-! ### The equilibrium is Markov in `(y_{t−1}, σε_t)` and the current regime -/

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the solution on the subtree below the date-`(t + 1)` node `s`,
re-indexed from that node. -/
def vfun (u : ℕ × Hist R → Y) (t : ℕ) (s : Hist R) : ℕ × Hist R → Y := fun n =>
  u (t + 1 + n.1, splice n.1 n.2 s)

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the subtree solution is an adapted bounded process. -/
theorem vfun_mem {u : Bd (ℕ × Hist R) Y} (hu : u ∈ adSub (R := R) Y) (t : ℕ) (s : Hist R) :
    (mkBd (vfun u t s) ⟨‖u‖, fun _ => norm_apply_le u _⟩ : Bd (ℕ × Hist R) Y) ∈
      adSub (R := R) Y := by
  refine ⟨fun m => (hu.1 (t + 1 + m)).comp_measurable (measurable_splice m s),
    fun m s1 s2 h1 h2 => ?_⟩
  have : splice m s1 s = splice m s2 s := by
    funext i
    simp only [splice]
    split_ifs with ha hb
    · exact h1 i ha
    · rw [h2]
    · rfl
  simp only [mkBd_apply, vfun, this]

omit [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [MeasurableSpace R]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the subtree below a date-`(t + 1)` node solves the model started
there, with predecessor `y_t`, current scaled shock `σ clip(ε_{t+1})` and the same `σ`. -/
theorem solves_vfun {u : ℕ × Hist R → Y} {p : Y × ℝ × ℝ} (hs : M.Solves u p) (t : ℕ)
    (s : Hist R) :
    M.Solves (vfun u t s) (u (t, tailH s), p.2.2 * clipB M.bound (s 0).2, p.2.2) := by
  intro m s''
  have key := hs (t + 1 + m) (splice m s'' s)
  have hreg : (splice m s'' s 0).1 = (s'' 0).1 := by
    rw [splice_zero_apply]
    split_ifs <;> rfl
  have hl : lagF (u (t, tailH s), p.2.2 * clipB M.bound (s 0).2, p.2.2) (vfun u t s) (m, s'') =
      lagF p u (t + 1 + m, splice m s'' s) := by
    cases m with
    | zero => simp [lagF, tailH_splice_zero]
    | succ m => simp [lagF, vfun, tailH_splice]
  have he : M.enowF (u (t, tailH s), p.2.2 * clipB M.bound (s 0).2, p.2.2) (m, s'') =
      M.enowF p (t + 1 + m, splice m s'' s) := by
    cases m with
    | zero => simp [enowF, splice]
    | succ m => simp [enowF, splice]
  rw [hreg] at key
  simp only [vfun, ← consH_splice, hl, he]
  exact key

omit [FiniteDimensional ℝ Y] [MeasurableSingletonClass R] [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium is Markov**): near `p̄`, at every date
`t + 1` and history `s`, `y_{t+1} = g(y_t, σ clip(ε_{t+1}), σ; ρ_{t+1})`, where
`g(y_{−1}, s₀, σ; r) = ψ(y_{−1}, s₀, σ)(0, r)` is the date-0 decision in regime `r` (the policy
function). -/
theorem markov {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := R) Y}
    (hψ : M.LocalSol ybar ψ) : ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ), ∀ t s,
      (ψ p : Bd (ℕ × Hist R) Y) (t + 1, s) =
        (ψ ((ψ p : Bd (ℕ × Hist R) Y) (t, tailH s), p.2.2 * clipB M.bound (s 0).2, p.2.2) :
          Bd (ℕ × Hist R) Y) (0, fun _ => ((s 0).1, 0)) := by
  obtain ⟨δ, hδ, huniq⟩ := hψ.unique
  have hB : 0 < 1 + |M.bound| := by positivity
  have hball : ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ), dist (ψ p) (ubar ybar) < δ := by
    have := hψ.cont.tendsto
    rw [hψ.base] at this
    exact this (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hψ.solves, hball, Metric.ball_mem_nhds (pbar ybar : Y × ℝ × ℝ)
    (div_pos hδ hB)] with p hs hd hp t s
  rw [Metric.mem_ball] at hp
  have hσ : |p.2.2| ≤ dist p (pbar ybar) := by
    rw [Prod.dist_eq, Prod.dist_eq]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    simp [pbar]
  have hδB : δ / (1 + |M.bound|) ≤ δ := div_le_self hδ.le (by linarith [abs_nonneg M.bound])
  set u : Bd (ℕ × Hist R) Y := (ψ p : Bd (ℕ × Hist R) Y) with hu
  set v : adSub (R := R) Y := ⟨mkBd (vfun u t s) ⟨‖u‖, fun n => norm_apply_le u _⟩,
    vfun_mem (ψ p).2 t s⟩ with hv
  set pn : Y × ℝ × ℝ := (u (t, tailH s), p.2.2 * clipB M.bound (s 0).2, p.2.2) with hpn
  have hdu : ∀ n, ‖u n - ybar‖ < δ := fun n => by
    refine lt_of_le_of_lt ?_ hd
    rw [dist_eq_norm]
    have := norm_apply_le ((ψ p : Bd (ℕ × Hist R) Y) -
      ((ubar ybar : adSub (R := R) Y) : Bd (ℕ × Hist R) Y)) n
    simpa [ubar] using this
  have hdv : dist v (ubar ybar) < δ := by
    refine lt_of_le_of_lt ?_ hd
    rw [dist_eq_norm, dist_eq_norm]
    refine norm_le_of_forall (norm_nonneg _) fun n => ?_
    have := norm_apply_le ((ψ p : Bd (ℕ × Hist R) Y) -
      ((ubar ybar : adSub (R := R) Y) : Bd (ℕ × Hist R) Y)) (t + 1 + n.1, splice n.1 n.2 s)
    simpa [ubar, hv, vfun] using this
  have hdp : dist pn (pbar ybar) < δ := by
    have hσδ : |p.2.2| < δ / (1 + |M.bound|) := lt_of_le_of_lt hσ hp
    have h1 : |p.2.2 * clipB M.bound (s 0).2| < δ := by
      rw [abs_mul]
      calc |p.2.2| * |clipB M.bound (s 0).2| ≤ |p.2.2| * (1 + |M.bound|) :=
            mul_le_mul_of_nonneg_left ((abs_clipB_le _ _).trans (by linarith)) (abs_nonneg _)
        _ < δ / (1 + |M.bound|) * (1 + |M.bound|) := mul_lt_mul_of_pos_right hσδ hB
        _ = δ := by field_simp
    rw [Prod.dist_eq, Prod.dist_eq]
    refine max_lt ?_ (max_lt ?_ ?_)
    · rw [dist_eq_norm]; exact hdu _
    · simpa [pbar, Real.dist_eq, hpn, abs_mul] using h1
    · simpa [pbar, Real.dist_eq] using lt_of_lt_of_le hσδ hδB
  have hsv : M.Solves (v : Bd (ℕ × Hist R) Y) pn := by
    have := M.solves_vfun hs t s
    exact this
  have h := congrArg
    (fun w : adSub (R := R) Y => (w : Bd (ℕ × Hist R) Y) (0, fun _ => ((s 0).1, 0)))
    (huniq pn v hdp hdv hsv)
  simp only at h
  rw [h]
  simp only [hv, mkBd_apply, vfun, add_zero, splice_zero_self]

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695 (**the implicit-function identity**): differentiating
`Φ(p, ψ(p)) = 0` at `p̄`, `DΦ(p̄, ȳ)(v, ψ′v) = 0` for every direction `v`. -/
theorem ift_identity [CompleteSpace Y] (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y}
    {ψ : Y × ℝ × ℝ → adSub (R := R) Y} (hψ : M.LocalSol ybar ψ)
    {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := R) Y} (hψd : HasFDerivAt ψ ψ' (pbar ybar))
    (v : Y × ℝ × ℝ) :
    fderiv ℝ (M.Phi hM hf.continuous) ((pbar ybar : Y × ℝ × ℝ), ubar ybar) (v, ψ' v) = 0 := by
  have hP : HasFDerivAt (M.Phi hM hf.continuous)
      (fderiv ℝ (M.Phi hM hf.continuous) ((pbar ybar : Y × ℝ × ℝ), ubar ybar))
      ((pbar ybar : Y × ℝ × ℝ), ψ (pbar ybar)) := by
    rw [hψ.base]
    exact ((M.contDiff_Phi hM hf).differentiable one_ne_zero _).hasFDerivAt
  have hin : HasFDerivAt (fun p : Y × ℝ × ℝ => (p, ψ p))
      ((ContinuousLinearMap.id ℝ (Y × ℝ × ℝ)).prod ψ') (pbar ybar) :=
    (hasFDerivAt_id _).prodMk hψd
  have hcomp := hP.comp (pbar ybar) hin
  have heq : (fun _ : Y × ℝ × ℝ => (0 : adSub (R := R) Z)) =ᶠ[𝓝 (pbar ybar : Y × ℝ × ℝ)]
      (M.Phi hM hf.continuous ∘ fun p => (p, ψ p)) := by
    filter_upwards [hψ.solves] with p hp
    exact ((M.Phi_eq_zero_iff hM hf.continuous p (ψ p)).2 hp).symm
  have hU := (hasFDerivAt_const (0 : adSub (R := R) Z) (pbar ybar : Y × ℝ × ℝ)).unique
    (hcomp.congr_of_eventuallyEq heq)
  have := congrArg (fun L : Y × ℝ × ℝ →L[ℝ] adSub (R := R) Z => L v) hU
  exact this.symm

/-! ### Determinacy excludes a unit root -/

omit [Fintype R] [MeasurableSingletonClass R] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. A.3, p. 632: the date-only tent process `φ_N(t) v`, adapted. -/
noncomputable def tentAd (N : ℕ) (v : Y) : adSub (R := R) Y :=
  ⟨mkBd (fun n => tent N n.1 • v) ⟨‖v‖, fun n => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_tent_le N _)⟩,
    fun t => (stronglyMeasurable_const : StronglyMeasurable fun _ : Hist R => tent N t • v),
    fun _ _ _ _ _ => rfl⟩

/-- Woodford (2003), App. A.3, p. 632: if `(A + B + C) v = 0`, the tent processes are approximate
kernel vectors of the linearised operator, `‖L(φ_N v)‖ ≤ (‖Av‖ + ‖Cv‖)/N`. -/
theorem norm_linOp_tentAd_le (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar v : Y}
    (hv : (M.dA ybar + M.dB ybar + M.dC ybar) v = 0) (N : ℕ) :
    ‖M.linOp hM hf.continuous ybar (tentAd N v)‖ ≤ (‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N := by
  have hB : M.dB ybar v = -M.dA ybar v - M.dC ybar v := by
    simp only [add_apply] at hv
    rw [← sub_eq_zero, ← hv]
    abel
  change ‖((M.linOp hM hf.continuous ybar (tentAd N v) : adSub (R := R) Z) :
    Bd (ℕ × Hist R) Z)‖ ≤ _
  refine norm_le_of_forall (by positivity) fun n => ?_
  rcases n with ⟨t, s⟩
  rw [M.linOp_apply hM hf.continuous hf ybar]
  have hlag : lagF (0 : Y × ℝ × ℝ) ((tentAd N v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (t, s) =
      (if t = 0 then 0 else tent N (t - 1)) • v := by
    cases t with
    | zero => simp [lagF]
    | succ t => simp [lagF, tentAd]
  have hconst : ∀ r' : R, ∫ e, (M.dA ybar (((tentAd N v : adSub (R := R) Y) :
      Bd (ℕ × Hist R) Y) (t + 1, consH (r', e) s)) +
      M.dB ybar (((tentAd N v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (t, s)) +
      M.dC ybar (lagF 0 ((tentAd N v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (t, s)))
      ∂(M.law r' : Measure ℝ) = tent N (t + 1) • M.dA ybar v + tent N t • M.dB ybar v +
        (if t = 0 then 0 else tent N (t - 1)) • M.dC ybar v := fun r' => by
    rw [hlag, map_smul]
    have e : ∀ e : ℝ, M.dA ybar (((tentAd N v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y)
        (t + 1, consH (r', e) s)) = tent N (t + 1) • M.dA ybar v := fun e => by
      simp [tentAd, map_smul]
    have e2 : M.dB ybar (((tentAd N v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y) (t, s)) =
        tent N t • M.dB ybar v := by simp [tentAd, map_smul]
    simp only [e, e2]
    rw [integral_const]
    simp
  simp only [hconst, ← Finset.sum_smul, hM.trans_sum, one_smul]
  rw [hB]
  have h1 := abs_tent_succ_sub N t
  have hN : (0 : ℝ) ≤ 1 / N := by positivity
  cases t with
  | zero =>
    simp only [tent_zero, zero_smul, add_zero, ↓reduceIte]
    rw [tent_zero, sub_zero, zero_add] at h1
    rw [norm_smul, Real.norm_eq_abs]
    calc |tent N 1| * ‖M.dA ybar v‖ ≤ 1 / N * ‖M.dA ybar v‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ (‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right (by linarith [norm_nonneg (M.dC ybar v)])
            (by positivity)
  | succ t =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    have h2 := abs_tent_succ_sub N t
    rw [abs_sub_comm] at h2
    have e : tent N (t + 1 + 1) • M.dA ybar v + tent N (t + 1) • (-M.dA ybar v - M.dC ybar v) +
        tent N t • M.dC ybar v = (tent N (t + 1 + 1) - tent N (t + 1)) • M.dA ybar v +
          (tent N t - tent N (t + 1)) • M.dC ybar v := by
      simp only [sub_smul, smul_sub, smul_neg]
      abel
    rw [e]
    calc ‖(tent N (t + 1 + 1) - tent N (t + 1)) • M.dA ybar v +
          (tent N t - tent N (t + 1)) • M.dC ybar v‖
        ≤ 1 / N * ‖M.dA ybar v‖ + 1 / N * ‖M.dC ybar v‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, Real.norm_eq_abs] <;>
          exact mul_le_mul_of_nonneg_right (by assumption) (norm_nonneg _)
      _ = (‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N := by ring

/-- Woodford (2003), App. A.3, eq. (A.9) (**determinacy excludes a unit root, general shock
laws**): if the linearised operator is invertible on the adapted processes, `A + B + C` is
injective. -/
theorem injective_ABC_of_isInvertible [Nonempty R] (hM : M.Std) (hf : ContDiff ℝ 1 M.f)
    {ybar : Y}
    (hL : (M.linOp hM hf.continuous ybar).IsInvertible) :
    Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar) := by
  intro a b hab
  set v := a - b with hvdef
  have hv : (M.dA ybar + M.dB ybar + M.dC ybar) v = 0 := by rw [map_sub, hab, sub_self]
  set K := ‖(M.linOp hM hf.continuous ybar).inverse‖ * (‖M.dA ybar v‖ + ‖M.dC ybar v‖) with hK
  have key : ∀ N : ℕ, 0 < N → ‖v‖ ≤ K / N := fun N hN => by
    have h1 : ‖v‖ = ‖((tentAd N v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y)
        (N, fun _ => Classical.arbitrary _)‖ := by
      rw [show ((tentAd N v : adSub (R := R) Y) : Bd (ℕ × Hist R) Y)
        (N, fun _ => Classical.arbitrary _) = tent N N • v from rfl, tent_self hN, one_smul]
    rw [h1]
    refine (norm_apply_le _ _).trans ?_
    change ‖tentAd (R := R) N v‖ ≤ _
    rw [← hL.inverse_apply_self (tentAd N v)]
    refine ((M.linOp hM hf.continuous ybar).inverse.le_opNorm _).trans ?_
    calc ‖(M.linOp hM hf.continuous ybar).inverse‖ *
          ‖M.linOp hM hf.continuous ybar (tentAd N v)‖
        ≤ ‖(M.linOp hM hf.continuous ybar).inverse‖ * ((‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N) :=
          mul_le_mul_of_nonneg_left (M.norm_linOp_tentAd_le hM hf hv N) (by positivity)
      _ = K / N := by rw [hK, mul_div_assoc]
  have hv0 : ‖v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (K / ‖v‖)
    have hN0 : 0 < N := by
      have : 0 ≤ K / ‖v‖ := div_nonneg (by positivity) hpos.le
      exact_mod_cast lt_of_le_of_lt this hN
    have h2 := key N hN0
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [div_lt_iff₀ hpos] at hN
    rw [le_div_iff₀ hNr] at h2
    linarith
  rw [norm_eq_zero, hvdef, sub_eq_zero] at hv0
  exact hv0

end MModel

/-! ## Certainty equivalence and the `σ²` correction for an i.i.d. law

A single regime (`R = Unit`): the shocks are i.i.d. with an ARBITRARY law `ν` (bounded support
through the clipping; e.g. a uniform, a truncated normal, or finitely many values). -/

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the clipped shock is integrable for any probability law. -/
theorem integrable_clipB (B : ℝ) (ν : ProbabilityMeasure ℝ) :
    Integrable (fun e => clipB B e) (ν : Measure ℝ) :=
  Integrable.of_bound (continuous_clipB B).aestronglyMeasurable |B|
    (Eventually.of_forall fun e => by rw [Real.norm_eq_abs]; exact abs_clipB_le B e)

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2: the squared clipped shock is integrable. -/
theorem integrable_clipB_sq (B : ℝ) (ν : ProbabilityMeasure ℝ) :
    Integrable (fun e => clipB B e ^ 2) (ν : Measure ℝ) :=
  Integrable.of_bound ((continuous_clipB B).pow 2).aestronglyMeasurable (|B| ^ 2)
    (Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_clipB_le B e) 2)

omit [MeasurableSpace R] in
/-- Woodford (2003), App. E.2 (expectations of quadratics in the shock): for a probability law,
`∫ (K₀ + c K₁ + c² K₂) = K₀ + E[c] K₁ + E[c²] K₂` with `c = clip(ε)`. -/
theorem integral_quad_clip {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (B : ℝ) (ν : ProbabilityMeasure ℝ) (K0 K1 K2 : V) :
    ∫ e, (K0 + clipB B e • K1 + clipB B e ^ 2 • K2) ∂(ν : Measure ℝ) =
      K0 + (∫ e, clipB B e ∂(ν : Measure ℝ)) • K1 +
        (∫ e, clipB B e ^ 2 ∂(ν : Measure ℝ)) • K2 := by
  have h1 : Integrable (fun e => K0 + clipB B e • K1) (ν : Measure ℝ) :=
    (integrable_const K0).add ((integrable_clipB B ν).smul_const K1)
  have e1 := integral_add h1 ((integrable_clipB_sq B ν).smul_const K2)
  have e2 := integral_add (integrable_const K0) ((integrable_clipB B ν).smul_const K1)
  rw [e1, e2, integral_const, integral_smul_const, integral_smul_const]
  simp

namespace MModel

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [CompleteSpace Z]

/-- Woodford (2003), App. E.2: the empty history of the single-regime model. -/
def sNil : Hist Unit := fun _ => ((), 0)

/-- Woodford (2003), App. E.2, p. 695 (**the policy function, i.i.d. shocks**):
`g(y_{−1}, s₀, σ) = ψ(y_{−1}, s₀, σ)` at date `0`. -/
def policyU (ψ : Y × ℝ × ℝ → adSub (R := Unit) Y) (p : Y × ℝ × ℝ) : Y :=
  (ψ p : Bd (ℕ × Hist Unit) Y) (0, sNil)

variable {N : MModel Unit Y Z}

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: in the single regime the transition probability is one. -/
theorem trans_unit (hN : N.Std) : N.trans () () = 1 := by
  simpa using hN.trans_sum ()

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, p. 695 (**Markov, i.i.d. shocks**): near `p̄`, the date-1
decision after the shock `e` is `g(y_0, σ clip(e), σ)`. -/
theorem markovU {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y} (hψ : N.LocalSol ybar ψ) :
    ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ), ∀ e : ℝ,
      (ψ p : Bd (ℕ × Hist Unit) Y) (1, consH ((), e) sNil) =
        policyU ψ ((ψ p : Bd (ℕ × Hist Unit) Y) (0, sNil), p.2.2 * clipB N.bound e, p.2.2) := by
  filter_upwards [N.markov hψ] with p hp e
  exact hp 0 (consH ((), e) sNil)

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2 (**differentiating the Markov property, i.i.d. shocks**): with
`G′ = Dg(p̄)`, the derivative of the solution at the date-1 node after `e` is
`G′(ψ′v(0), v_σ clip(e), v_σ)`. -/
theorem markov_derivU {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := Unit) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {G' : Y × ℝ × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policyU ψ) G' (pbar ybar)) (v : Y × ℝ × ℝ) (e : ℝ) :
    (ψ' v : Bd (ℕ × Hist Unit) Y) (1, consH ((), e) sNil) =
      G' ((ψ' v : Bd (ℕ × Hist Unit) Y) (0, sNil), v.2.2 * clipB N.bound e, v.2.2) := by
  set ev : ℕ × Hist Unit → adSub (R := Unit) Y →L[ℝ] Y := fun n =>
    (evalL Y n).comp (adSub (R := Unit) Y).subtypeL with hev
  have hin : HasFDerivAt (fun p : Y × ℝ × ℝ =>
      ((ψ p : Bd (ℕ × Hist Unit) Y) (0, sNil), p.2.2 * clipB N.bound e, p.2.2))
      (((ev (0, sNil)).comp ψ').prod
        (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ))).smulRight
          (clipB N.bound e) |>.prod
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ)))))
      (pbar ybar) := by
    refine ((ev (0, sNil)).hasFDerivAt.comp _ hψd).prodMk ?_
    refine HasFDerivAt.prodMk ?_ ?_
    · have := (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ))).smulRight (clipB N.bound e)).hasFDerivAt
        (x := (pbar ybar : Y × ℝ × ℝ))
      convert this using 1
      funext p
      simp [smul_eq_mul]
    · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ Y (ℝ × ℝ))).hasFDerivAt
  have hval : ((ψ (pbar ybar) : Bd (ℕ × Hist Unit) Y) (0, sNil),
      (pbar ybar : Y × ℝ × ℝ).2.2 * clipB N.bound e, (pbar ybar : Y × ℝ × ℝ).2.2) =
      (pbar ybar : Y × ℝ × ℝ) := by
    rw [hψ.base]
    simp [pbar, ubar]
  rw [← hval] at hg
  have hR := hg.comp (pbar ybar) hin
  have hL : HasFDerivAt (fun p => (ψ p : Bd (ℕ × Hist Unit) Y) (1, consH ((), e) sNil))
      ((ev (1, consH ((), e) sNil)).comp ψ') (pbar ybar) :=
    (ev (1, consH ((), e) sNil)).hasFDerivAt.comp _ hψd
  have heq : (fun p => (ψ p : Bd (ℕ × Hist Unit) Y) (1, consH ((), e) sNil)) =ᶠ[𝓝 (pbar ybar)]
      (policyU ψ ∘ fun p : Y × ℝ × ℝ =>
        ((ψ p : Bd (ℕ × Hist Unit) Y) (0, sNil), p.2.2 * clipB N.bound e, p.2.2)) := by
    filter_upwards [markovU hψ] with p hp
    exact hp e
  have hU := hL.unique (hR.congr_of_eventuallyEq heq)
  have := congrArg (fun L : Y × ℝ × ℝ →L[ℝ] Y => L v) hU
  simpa [hev, mul_comm] using this

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2 (**the first-order identity at the root, i.i.d. shocks**): with
`G′ = Dg(p̄)`, for every direction `v`,
`∫ Df(z̄)(G′(G′v, v_σ clip(e), v_σ), G′v, v_y, v_s, v_σ clip(e)) dν(e) = 0`. -/
theorem root_identity_iid [CompleteSpace Y] [FiniteDimensional ℝ Y] [CompleteSpace Z]
    (hN : N.Std)
    (hf : ContDiff ℝ 1 N.f) {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := Unit) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {G' : Y × ℝ × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policyU ψ) G' (pbar ybar)) (v : Y × ℝ × ℝ) :
    ∫ e, fderiv ℝ N.f (zbar ybar) (G' (G' v, v.2.2 * clipB N.bound e, v.2.2), G' v, v.1, v.2.1,
      v.2.2 * clipB N.bound e) ∂(N.law () : Measure ℝ) = 0 := by
  have hG : G' = ((evalL Y (0, sNil)).comp (adSub (R := Unit) Y).subtypeL).comp ψ' :=
    hg.unique (((evalL Y (0, sNil)).comp (adSub (R := Unit) Y).subtypeL).hasFDerivAt.comp _ hψd)
  have hroot : (ψ' v : Bd (ℕ × Hist Unit) Y) (0, sNil) = G' v := by rw [hG]; rfl
  have hI := congrArg (fun w : adSub (R := Unit) Z => (w : Bd (ℕ × Hist Unit) Z) (0, sNil))
    (N.ift_identity hN hf hψ hψd v)
  simp only at hI
  rw [N.fderiv_Phi_apply hN hf.continuous hf ybar] at hI
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton] at hI
  rw [show sNil 0 = ((), (0 : ℝ)) from rfl, trans_unit hN, one_smul] at hI
  have hw : ∀ e : ℝ, N.wfun v ((ψ' v : adSub (R := Unit) Y) : Bd (ℕ × Hist Unit) Y)
      (0 + 1, consH ((), e) sNil) = (G' (G' v, v.2.2 * clipB N.bound e, v.2.2), G' v, v.1,
        v.2.1, v.2.2 * clipB N.bound e) := fun e => by
    simp only [wfun, tailH_consH, consH_zero, lagF, enowF]
    rw [hroot, show (0 : ℕ) + 1 = 1 from rfl, markov_derivU hψ hψd hg v e, hroot]
  simp only [hw] at hI
  exact hI

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2: the first-order identity in the lag direction, the matrix
quadratic `A G_y² + B G_y + C = 0` (`G_y = G′(·, 0, 0)`). -/
theorem first_order_lag_iid [CompleteSpace Z] [CompleteSpace Y] [FiniteDimensional ℝ Y]
    (hN : N.Std) (hf : ContDiff ℝ 1 N.f) {ybar : Y} {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := Unit) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {G' : Y × ℝ × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policyU ψ) G' (pbar ybar)) (h : Y) :
    N.dA ybar (G' (G' (h, 0, 0), 0, 0)) + N.dB ybar (G' (h, 0, 0)) + N.dC ybar h = 0 := by
  have hr := root_identity_iid hN hf hψ hψd hg (h, 0, 0)
  simp only [zero_mul, integral_const, probReal_univ, one_smul, fderiv_f_apply, map_zero,
    add_zero] at hr
  exact hr

omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, and the perturbation method (**certainty equivalence for an
ARBITRARY i.i.d. law of bounded support**): if the clipped shock has mean zero and the
linearised operator is invertible (determinacy), then `g_σ(ȳ, 0, 0) = 0`. -/
theorem certainty_equivalence_iid [CompleteSpace Z] [CompleteSpace Y] [FiniteDimensional ℝ Y]
    (hN : N.Std) (hf : ContDiff ℝ 1 N.f) {ybar : Y}
    (hL : (N.linOp hN hf.continuous ybar).IsInvertible) {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) {ψ' : Y × ℝ × ℝ →L[ℝ] adSub (R := Unit) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {G' : Y × ℝ × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policyU ψ) G' (pbar ybar))
    (hmean : ∫ e, clipB N.bound e ∂(N.law () : Measure ℝ) = 0) : G' (0, 0, 1) = 0 := by
  have hinj := N.injective_ABC_of_isInvertible hN hf hL
  set G : Y →L[ℝ] Y := G'.comp (ContinuousLinearMap.inl ℝ Y (ℝ × ℝ)) with hGd
  have hGa : ∀ a, G a = G' (a, 0, 0) := fun a => rfl
  refine SmoothInSigma.Model.ce_algebra (A := N.dA ybar) (B := N.dB ybar) (C := N.dC ybar)
    (G := G) (fun h => by rw [hGa, hGa]; exact first_order_lag_iid hN hf hψ hψd hg h) hinj ?_
  have hr := root_identity_iid hN hf hψ hψd hg (0, 0, 1)
  set c := G' (0, 0, 1) with hc
  have e : ∀ e : ℝ, fderiv ℝ N.f (zbar ybar) (G' (c, 1 * clipB N.bound e, 1), c, 0, 0,
      1 * clipB N.bound e) = (N.dA ybar (G c) + N.dA ybar c + N.dB ybar c) +
        clipB N.bound e • (N.dA ybar (G' (0, 1, 0)) + N.dE ybar 1) +
        clipB N.bound e ^ 2 • (0 : Z) := fun e => by
    rw [fderiv_f_apply, SmoothInSigma.Model.clm_triple G' c, hGa]
    have h1 : G' (0, clipB N.bound e, 0) = clipB N.bound e • G' (0, 1, 0) := by
      rw [← map_smul]; simp
    have h2 : N.dE ybar (clipB N.bound e) = clipB N.bound e • N.dE ybar 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    simp only [one_mul, h1, h2, map_add, map_smul, one_smul, map_zero, smul_zero, add_zero,
      smul_add]
    abel
  rw [show (fun e => fderiv ℝ N.f (zbar ybar) (G' (G' (0, 0, 1), 1 * clipB N.bound e, 1),
      G' (0, 0, 1), 0, 0, 1 * clipB N.bound e)) = fun e => (N.dA ybar (G c) + N.dA ybar c +
        N.dB ybar c) + clipB N.bound e • (N.dA ybar (G' (0, 1, 0)) + N.dE ybar 1) +
        clipB N.bound e ^ 2 • (0 : Z) from funext e] at hr
  rw [integral_quad_clip, hmean, zero_smul, smul_zero, add_zero, add_zero] at hr
  exact hr

set_option maxHeartbeats 2000000 in
-- the chain of node identities and second derivatives is long to elaborate
omit [CompleteSpace Z] in
/-- Woodford (2003), App. E.2, and the second-order perturbation equation (**the `σ²` correction
for an ARBITRARY i.i.d. law of bounded support**): with `g` the policy function, `G′ = Dg(p̄)`,
`g″ = D²g(p̄)`, `g_σσ = g″(e_σ, e_σ)`, `G_s = G′(0, 1, 0)` (response to the current shock),
`G_ss = g″((0,1,0),(0,1,0))`, and `V = E[clip(ε)²]` (the variance),
`(A G_y + A + B) g_σσ + V [A G_ss + D²f(z̄)((G_s, 0, 0, 0, 1), (G_s, 0, 0, 0, 1))] = 0`,
under mean-zero shocks and determinacy. -/
theorem second_order_sigma_iid [CompleteSpace Z] [CompleteSpace Y] [FiniteDimensional ℝ Y]
    (hN : N.Std) (hf : ContDiff ℝ 2 N.f) {ybar : Y}
    (hL : (N.linOp hN hf.continuous ybar).IsInvertible) {ψ : Y × ℝ × ℝ → adSub (R := Unit) Y}
    (hψ : N.LocalSol ybar ψ) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (hmean : ∫ e, clipB N.bound e ∂(N.law () : Measure ℝ) = 0) :
    N.dA ybar (fderiv ℝ (policyU ψ) (pbar ybar)
        (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1), 0, 0)) +
      N.dA ybar (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      N.dB ybar (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      (∫ e, clipB N.bound e ^ 2 ∂(N.law () : Measure ℝ)) •
        (N.dA ybar (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, 1, 0) (0, 1, 0)) +
          fderiv ℝ (fderiv ℝ N.f) (zbar ybar)
            (fderiv ℝ (policyU ψ) (pbar ybar) (0, 1, 0), 0, 0, 0, 1)
            (fderiv ℝ (policyU ψ) (pbar ybar) (0, 1, 0), 0, 0, 0, 1)) = 0 := by
  obtain ⟨e3, he3⟩ : ∃ e3 : Y × ℝ × ℝ, e3 = (0, 0, 1) := ⟨_, rfl⟩
  rw [← he3]
  have hf1 : ContDiff ℝ 1 N.f := hf.of_le (by norm_num)
  set ev : ℕ × Hist Unit → adSub (R := Unit) Y →L[ℝ] Y := fun n =>
    (evalL Y n).comp (adSub (R := Unit) Y).subtypeL with hev
  set evZ : ℕ × Hist Unit → adSub (R := Unit) Z →L[ℝ] Z := fun n =>
    (evalL Z n).comp (adSub (R := Unit) Z).subtypeL with hevZ
  set evW : ℕ × Hist Unit → adSub (R := Unit) (Y × Y × Y × ℝ × ℝ) →L[ℝ] Y × Y × Y × ℝ × ℝ :=
    fun n => (evalL (Y × Y × Y × ℝ × ℝ) n).comp
      (adSub (R := Unit) (Y × Y × Y × ℝ × ℝ)).subtypeL with hevW
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (pbar ybar)) (pbar ybar) :=
    (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hψev : ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ), HasFDerivAt ψ (fderiv ℝ ψ p) p :=
    (hψ2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hψF1 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (pbar ybar) :=
    ((hψ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg2 : ContDiffAt ℝ 2 (policyU ψ) (pbar ybar) :=
    (ev (0, sNil)).contDiff.contDiffAt.comp (pbar ybar) hψ2
  have hgd : HasFDerivAt (policyU ψ) (fderiv ℝ (policyU ψ) (pbar ybar)) (pbar ybar) :=
    (hg2.differentiableAt (by norm_num)).hasFDerivAt
  have hgev : ∀ᶠ p in 𝓝 (pbar ybar : Y × ℝ × ℝ),
      HasFDerivAt (policyU ψ) (fderiv ℝ (policyU ψ) p) p :=
    (hg2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hgF1 : HasFDerivAt (fderiv ℝ (policyU ψ)) (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar))
      (pbar ybar) :=
    ((hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hfd : ∀ z, HasFDerivAt N.f (fderiv ℝ N.f z) z := fun z =>
    (hf.differentiable (by norm_num) z).hasFDerivAt
  have hfF1 : HasFDerivAt (fderiv ℝ N.f) (fderiv ℝ (fderiv ℝ N.f) (zbar ybar)) (zbar ybar) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _).hasFDerivAt
  have hce : fderiv ℝ (policyU ψ) (pbar ybar) e3 = 0 := by
    rw [he3]
    exact certainty_equivalence_iid hN hf1 hL hψ hψd hgd hmean
  have hg'eq : fderiv ℝ (policyU ψ) (pbar ybar) = (ev (0, sNil)).comp (fderiv ℝ ψ (pbar ybar)) :=
    hgd.unique ((ev (0, sNil)).hasFDerivAt.comp (pbar ybar) hψd)
  have hsm : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) (s : ℝ),
      HasDerivAt (fun s : ℝ => s • v) v s := fun v s => by
    simpa using (hasDerivAt_id s).smul_const v
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Y × ℝ × ℝ, γ = fun s => (ybar, 0, s) := ⟨_, rfl⟩
  have hγd : ∀ s, HasDerivAt γ e3 s := fun s => by
    rw [hγ, he3]
    exact (hasDerivAt_const s ybar).prodMk ((hasDerivAt_const s (0 : ℝ)).prodMk (hasDerivAt_id s))
  have hγ0 : γ 0 = pbar ybar := by rw [hγ]; rfl
  have hγt : Tendsto γ (𝓝 0) (𝓝 (pbar ybar)) := hγ0 ▸ (hγd 0).continuousAt.tendsto
  obtain ⟨u, hu⟩ : ∃ u : ℝ → adSub (R := Unit) Y, u = fun s => ψ (γ s) := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ → adSub (R := Unit) Y, u1 = fun s => fderiv ℝ ψ (γ s) e3 :=
    ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2 : adSub (R := Unit) Y,
      u2 = fderiv ℝ (fderiv ℝ ψ) (pbar ybar) e3 e3 := ⟨_, rfl⟩
  have hud : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt u (u1 s) s := by
    rw [hu, hu1]
    filter_upwards [hγt.eventually hψev] with s hs
    exact hs.comp_hasDerivAt s (hγd s)
  have hu1d : HasDerivAt u1 u2 0 := by
    have hF : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (γ 0) := by
      rw [hγ0]; exact hψF1
    have h0 := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := Y × ℝ × ℝ)
      (E := (Y × ℝ × ℝ) →L[ℝ] adSub (R := Unit) Y) (f := γ) (l := fderiv ℝ ψ) (0 : ℝ) hF (hγd 0)
    have h1 := (ContinuousLinearMap.apply ℝ (adSub (R := Unit) Y) e3).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) h0
    rw [hu1, hu2]
    exact h1
  have hun : ∀ n, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s => ev n (u s)) (ev n (u1 s)) s :=
    fun n => hud.mono fun s hs => (ev n).hasFDerivAt.comp_hasDerivAt s hs
  have hun1 : ∀ n, HasDerivAt (fun s => ev n (u1 s)) (ev n u2) 0 := fun n =>
    (ev n).hasFDerivAt.comp_hasDerivAt 0 hu1d
  have hu0 : u 0 = ubar ybar := by rw [hu]; simp only [hγ0]; exact hψ.base
  have hu10 : u1 0 = fderiv ℝ ψ (pbar ybar) e3 := by rw [hu1]; simp only [hγ0]
  -- the root: `u s (0) = g (γ s)` exactly
  have hR0 : ev (0, sNil) u2 = fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) e3 e3 := by
    have hF : ∀ᶠ x in 𝓝 (γ 0), HasFDerivAt (policyU ψ) (fderiv ℝ (policyU ψ) x) x := by
      rw [hγ0]; exact hgev
    have hF1 : HasFDerivAt (fderiv ℝ (policyU ψ)) (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar))
        (γ 0) := by rw [hγ0]; exact hgF1
    have := SmoothInSigma.Model.secondDeriv_comp (F := policyU ψ) (a := γ) (a1 := fun _ => e3)
      (a2 := 0) (y := fun s => ev (0, sNil) (u s)) (y1 := fun s => ev (0, sNil) (u1 s)) hF hF1
      (Eventually.of_forall hγd) (hasDerivAt_const 0 e3) (hun _) (hun1 _)
      (Eventually.of_forall fun s => by rw [hu]; rfl)
    rw [this, map_zero, add_zero]
  have h1root : ev (0, sNil) (u1 0) = 0 := by
    rw [hu10, ← hce, hg'eq]
    rfl
  have h1child : ∀ e : ℝ, ev (1, consH ((), e) sNil) (u1 0) =
      clipB N.bound e • fderiv ℝ (policyU ψ) (pbar ybar) (0, 1, 0) := fun e => by
    have h := markov_derivU hψ hψd hgd e3 e
    rw [hu10]
    change ((fderiv ℝ ψ (pbar ybar) e3 : adSub (R := Unit) Y) : Bd (ℕ × Hist Unit) Y)
      (1, consH ((), e) sNil) = _
    rw [h]
    have h0 : ((fderiv ℝ ψ (pbar ybar) e3 : adSub (R := Unit) Y) : Bd (ℕ × Hist Unit) Y)
        (0, sNil) = 0 := by rw [← hu10]; exact h1root
    rw [h0, he3]
    simp only [one_mul]
    rw [SmoothInSigma.Model.clm_triple, ← he3, hce, smul_zero, add_zero, Prod.mk_zero_zero,
      Prod.mk_zero_zero, map_zero, zero_add, show ((0 : Y), clipB N.bound e, (0 : ℝ)) =
        clipB N.bound e • ((0 : Y), (1 : ℝ), (0 : ℝ)) by simp, map_smul]
  -- the successors: `u s (1, e) = g(u s (0), s clip(e), s)` (Markov)
  have hRj : ∀ e : ℝ, ev (1, consH ((), e) sNil) u2 =
      fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) (0, clipB N.bound e, 1)
        (0, clipB N.bound e, 1) + fderiv ℝ (policyU ψ) (pbar ybar) (ev (0, sNil) u2, 0, 0) :=
    fun e => by
    obtain ⟨b, hb⟩ : ∃ b : ℝ → Y × ℝ × ℝ, b = fun s =>
        (ev (0, sNil) (u s), s * clipB N.bound e, s) := ⟨_, rfl⟩
    have hb0 : b 0 = pbar ybar := by
      rw [hb]
      change (ev (0, sNil) (u 0), (0 : ℝ) * clipB N.bound e, (0 : ℝ)) = pbar ybar
      rw [hu0, zero_mul]
      rfl
    have hF : ∀ᶠ x in 𝓝 (b 0), HasFDerivAt (policyU ψ) (fderiv ℝ (policyU ψ) x) x := by
      rw [hb0]; exact hgev
    have hF1 : HasFDerivAt (fderiv ℝ (policyU ψ)) (fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar))
        (b 0) := by rw [hb0]; exact hgF1
    have hmc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s * clipB N.bound e) (clipB N.bound e) s :=
      fun s => by simpa using (hasDerivAt_id s).mul_const (clipB N.bound e)
    have ha : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt b (ev (0, sNil) (u1 s), clipB N.bound e, 1) s := by
      rw [hb]
      exact (hun (0, sNil)).mono fun s hs => hs.prodMk ((hmc s).prodMk (hasDerivAt_id s))
    have ha1 : HasDerivAt (fun s => (ev (0, sNil) (u1 s), clipB N.bound e, (1 : ℝ)))
        (ev (0, sNil) u2, 0, 0) 0 :=
      (hun1 _).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
    have heq : ∀ᶠ s in 𝓝 (0 : ℝ), ev (1, consH ((), e) sNil) (u s) = policyU ψ (b s) := by
      filter_upwards [hγt.eventually (markovU hψ)] with s hs
      have h := hs e
      rw [hγ] at h
      rw [hb, hu, hγ]
      exact h
    have := SmoothInSigma.Model.secondDeriv_comp hF hF1 ha ha1 (hun _) (hun1 _) heq
    rw [this, hb0, h1root]
  -- the residual curve `H(s) = f(w(s))` on the adapted families
  have hγc : ContDiffAt ℝ 2 γ 0 := by rw [hγ]; fun_prop
  have huc : ContDiffAt ℝ 2 u 0 := by
    rw [hu]
    have : ContDiffAt ℝ 2 ψ (γ 0) := by rw [hγ0]; exact hψ2
    exact this.comp 0 hγc
  obtain ⟨cf, hcf⟩ : ∃ cf : ℝ → adSub (R := Unit) (Y × Y × Y × ℝ × ℝ),
      cf = fun s => N.WmapL (γ s, u s) := ⟨_, rfl⟩
  have hcc : ContDiffAt ℝ 2 cf 0 := by
    rw [hcf]
    exact (N.WmapL (R := Unit)).contDiff.contDiffAt.comp 0 (hγc.prodMk huc)
  obtain ⟨H, hH⟩ : ∃ H : ℝ → adSub (R := Unit) Z, H = fun s => N.NmS hf.continuous (cf s) :=
    ⟨_, rfl⟩
  have hHc : ContDiffAt ℝ 2 H 0 := by
    rw [hH]
    exact (N.contDiff_NmS hf).contDiffAt.comp 0 hcc
  have hHd : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt H (fderiv ℝ H s 1) s :=
    (hHc.eventually (by simp)).mono fun s hs =>
      (hs.differentiableAt (by norm_num)).hasFDerivAt.hasDerivAt
  have hFD : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) 0) 0 :=
    ((hHc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hH1d : HasDerivAt (fun s => fderiv ℝ H s 1) (fderiv ℝ (fderiv ℝ H) 0 1 1) 0 := by
    have h0 : HasDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) 0 1) 0 := hFD.hasDerivAt
    exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ →L[ℝ] adSub (R := Unit) Z)
      (E := adSub (R := Unit) Z) (f := fderiv ℝ H)
      (l := ContinuousLinearMap.apply ℝ (adSub (R := Unit) Z) (1 : ℝ)) (0 : ℝ)
      (ContinuousLinearMap.apply ℝ (adSub (R := Unit) Z) (1 : ℝ)).hasFDerivAt h0
  have hzero : ∀ᶠ s in 𝓝 (0 : ℝ), N.AvgL hN (H s) = 0 := by
    filter_upwards [hγt.eventually hψ.solves] with s hs
    have := (N.Phi_eq_zero_iff hN hf.continuous (γ s) (ψ (γ s))).2 hs
    rw [hH, hcf, hu]
    exact this
  have hAvg : N.AvgL hN (fderiv ℝ (fderiv ℝ H) 0 1 1) = 0 := by
    have := SmoothInSigma.Model.secondDeriv_comp (F := fun x => N.AvgL hN x)
      (F1 := fun _ => N.AvgL hN) (F2 := 0) (a := H) (a1 := fun s => fderiv ℝ H s 1)
      (a2 := fderiv ℝ (fderiv ℝ H) 0 1 1) (y := fun _ => (0 : adSub (R := Unit) Z))
      (y1 := fun _ => 0) (y2 := 0) (Eventually.of_forall fun x => (N.AvgL hN).hasFDerivAt)
      (hasFDerivAt_const _ _) hHd hH1d (Eventually.of_forall fun s => hasDerivAt_const s _)
      (hasDerivAt_const _ _) (hzero.mono fun s hs => hs.symm)
    simpa using this.symm
  set f2 := fderiv ℝ (fderiv ℝ N.f) (zbar ybar) with hf2
  have hnode : ∀ e : ℝ, evZ (1, consH ((), e) sNil) (fderiv ℝ (fderiv ℝ H) 0 1 1) =
      f2 (ev (1, consH ((), e) sNil) (u1 0), ev (0, sNil) (u1 0), 0, 0, clipB N.bound e)
        (ev (1, consH ((), e) sNil) (u1 0), ev (0, sNil) (u1 0), 0, 0, clipB N.bound e) +
      fderiv ℝ N.f (zbar ybar) (ev (1, consH ((), e) sNil) u2, ev (0, sNil) u2, 0, 0, 0) :=
    fun e => by
    have hmc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s * clipB N.bound e) (clipB N.bound e) s :=
      fun s => by simpa using (hasDerivAt_id s).mul_const (clipB N.bound e)
    have hae : (fun s => evW (1, consH ((), e) sNil) (cf s)) = fun s =>
        (ev (1, consH ((), e) sNil) (u s), ev (0, sNil) (u s), ybar, (0 : ℝ),
          s * clipB N.bound e) := by
      funext s
      rw [hcf, hγ]
      rfl
    have ha0 : (fun s => (ev (1, consH ((), e) sNil) (u s), ev (0, sNil) (u s), ybar, (0 : ℝ),
        s * clipB N.bound e)) 0 = zbar ybar := by
      simp only [zero_mul]
      rw [hu0]
      rfl
    have hF1 : HasFDerivAt (fderiv ℝ N.f) f2 ((fun s => (ev (1, consH ((), e) sNil) (u s),
        ev (0, sNil) (u s), ybar, (0 : ℝ), s * clipB N.bound e)) 0) := by rw [ha0]; exact hfF1
    have := SmoothInSigma.Model.secondDeriv_comp (F := N.f) (F1 := fderiv ℝ N.f) (F2 := f2)
      (a := fun s => (ev (1, consH ((), e) sNil) (u s), ev (0, sNil) (u s), ybar, (0 : ℝ),
        s * clipB N.bound e))
      (a1 := fun s => (ev (1, consH ((), e) sNil) (u1 s), ev (0, sNil) (u1 s), (0 : Y), (0 : ℝ),
        clipB N.bound e))
      (a2 := (ev (1, consH ((), e) sNil) u2, ev (0, sNil) u2, (0 : Y), (0 : ℝ), (0 : ℝ)))
      (y := fun s => evZ (1, consH ((), e) sNil) (H s))
      (y1 := fun s => evZ (1, consH ((), e) sNil) (fderiv ℝ H s 1))
      (Eventually.of_forall fun x => hfd x) hF1
      (((hun _).and (hun _)).mono fun s hs => hs.1.prodMk (hs.2.prodMk
        ((hasDerivAt_const s ybar).prodMk ((hasDerivAt_const s (0 : ℝ)).prodMk (hmc s)))))
      ((hun1 _).prodMk ((hun1 _).prodMk ((hasDerivAt_const _ _).prodMk
        ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _)))))
      (hHd.mono fun s hs => (evZ _).hasFDerivAt.comp_hasDerivAt s hs)
      ((evZ _).hasFDerivAt.comp_hasDerivAt 0 hH1d)
      (Eventually.of_forall fun s => by
        rw [← congrFun hae s, hH]
        rfl)
    rw [this, show (ev (1, consH ((), e) sNil) (u 0), ev (0, sNil) (u 0), ybar, (0 : ℝ),
      0 * clipB N.bound e) = zbar ybar from ha0]
  -- the root of the averaged identity
  have hroot := congrArg (fun w : adSub (R := Unit) Z => (w : Bd (ℕ × Hist Unit) Z) (0, sNil))
    hAvg
  simp only [AvgL_apply, avgFun, Finset.univ_unique, PUnit.default_eq_unit,
    Finset.sum_singleton] at hroot
  rw [show sNil 0 = ((), (0 : ℝ)) from rfl, trans_unit hN, one_smul] at hroot
  have hint : ∫ e, evZ (1, consH ((), e) sNil) (fderiv ℝ (fderiv ℝ H) 0 1 1)
      ∂(N.law () : Measure ℝ) = 0 := by
    simp only [ZeroMemClass.coe_zero] at hroot
    exact hroot
  set Gs := fderiv ℝ (policyU ψ) (pbar ybar) (0, 1, 0) with hGs
  set D2 := fderiv ℝ (fderiv ℝ (policyU ψ)) (pbar ybar) with hD2
  set gss := D2 e3 e3 with hgss
  have hsplit : ∀ c : ℝ, ((0 : Y), c, (1 : ℝ)) = c • ((0 : Y), (1 : ℝ), (0 : ℝ)) + e3 :=
    fun c => by rw [he3]; ext <;> simp
  have hz : ∀ c : ℝ, ((c • Gs, (0 : Y), (0 : Y), (0 : ℝ), c) : Y × Y × Y × ℝ × ℝ) =
      c • ((Gs, (0 : Y), (0 : Y), (0 : ℝ), (1 : ℝ)) : Y × Y × Y × ℝ × ℝ) := fun c => by
    ext <;> simp
  have hpt : ∀ e : ℝ, evZ (1, consH ((), e) sNil) (fderiv ℝ (fderiv ℝ H) 0 1 1) =
      (N.dA ybar (fderiv ℝ (policyU ψ) (pbar ybar) (gss, 0, 0)) + N.dA ybar gss +
        N.dB ybar gss) +
      clipB N.bound e • N.dA ybar (D2 ((0 : Y), (1 : ℝ), (0 : ℝ)) e3 +
        D2 e3 ((0 : Y), (1 : ℝ), (0 : ℝ))) +
      clipB N.bound e ^ 2 • (N.dA ybar (D2 ((0 : Y), (1 : ℝ), (0 : ℝ))
        ((0 : Y), (1 : ℝ), (0 : ℝ))) +
        f2 (Gs, 0, 0, 0, 1) (Gs, 0, 0, 0, 1)) := fun e => by
    rw [hnode e, h1child e, h1root, hRj e, hR0, hsplit (clipB N.bound e), hz]
    simp only [fderiv_f_apply, map_zero, add_zero, map_add, map_smul,
      add_apply, smul_apply, ← hgss]
    module
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_quad_clip, hmean, zero_smul,
    add_zero] at hint
  rw [he3, ← hint]

end MModel

end Woodford.StabilizationWelfare.SmoothInSigmaMeasure
