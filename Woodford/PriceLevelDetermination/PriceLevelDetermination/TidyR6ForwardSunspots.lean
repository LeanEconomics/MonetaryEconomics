/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.SunspotsNotOntoExamples

/-!
# Sunspots of `n`-dimensional forward systems decided by the nonlinear terms

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 632–634 (indeterminacy and sunspot
equilibria near a steady state). For the `n`-dimensional forward system
`E_t[x_{t+1} − g(x_t)] = 0` (`Gfwd`, all variables jumps, `g(0) = 0`) this module gives
conditions on the **nonlinear map `g` itself** — not on its linearisation — that decide whether
random sunspot equilibria exist near the steady state. They apply whatever the shape of the
operator (A.8) (unit roots, non-closed range, …) and are the tools of the leading-coefficient
criterion in `TidyR6CriticalCriterion`.

## Main results

* `unique_of_repelAnn`: if `g` is **repelling on annuli** (`RepelAnn`: on every annulus
  `B/2 ≤ ‖v‖ ≤ B` with `B ≤ r`, `‖g v‖ ≥ ‖v‖ + δ(B)`), then under informational closure (perfect
  foresight, every finite tree) the steady state is the only bounded adapted equilibrium within
  `r` of it (the system has no predetermined variable or disturbance);
  `unique_of_repelAnn_global` for every scale.
* `coin_eq_zero_of_two_step`: on the core coin tree, if only the **two-step map** `g ∘ g` is
  repelling on annuli and `g` vanishes only at `0` near `0`, every equilibrium within `r` is the
  steady state from date `1` on; hence `no_coin_sunspot_of_two_step`.
* `coin_sunspot_of_pair`: if a set `A` is mapped into itself by `g ∘ g` without increasing the
  norm, `‖g v‖ ≤ L‖v‖` on `A`, and two points `y₁ ≠ y₂` of `A` average to `g(c)`, then the coin
  tree has a genuinely random equilibrium (`x_0 = c`, `x_1 = y₁` or `y₂`, then `x_{t+1} = g(x_t)`).

Only the core expectation axioms and informational closure are used.
-/

namespace Woodford.PriceLevelDetermination.TidyR6ForwardSunspots

open scoped Topology
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic
open LocalIFTSystems (Arg)
open ExpectationsFiniteTree (coinSystem)

variable {ι : Type*} [Fintype ι]

/-! ### The forward system -/

/-- Woodford (2003), App. A.3, eq. (A.11), p. 633: the `n`-dimensional forward condition
`x_{t+1} − g(x_t)`, i.e. the system `E_t[x_{t+1} − g(x_t)] = 0` (no predetermined variable, no
disturbance). -/
def Gfwd (g : (ι → ℝ) → (ι → ℝ)) (p : Arg ι ℝ) : ι → ℝ := p.2.2.1 - g p.2.1

variable {Ω : Type*} {𝔼 : ExpectationSystem Ω}

/-- Woodford (2003), App. A.3, p. 633 (tool): under informational closure a function of a
vector known at `t` is known at `t`. -/
theorem known_vec (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {x : SProcV ι Ω} {t : ℕ}
    (hx : ∀ i, 𝔼.E t (toP x t i) = toP x t i) (f : (ι → ℝ) → ℝ) :
    𝔼.E t (fun ω => f (x (t, ω))) = fun ω => f (x (t, ω)) :=
  hcl t _ fun ω ω' h => by
    have e : x (t, ω) = x (t, ω') :=
      funext fun i => LocalIFTStochastic.Ops.cellConst_of_known 𝔼 (hx i) ω ω' h
    rw [e]

/-- Woodford (2003), App. A.3, p. 634 (tool): in an equilibrium of the forward system under
informational closure, `E_t x_{t+1} = g(x_t)`. -/
theorem fwd_E (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {g : (ι → ℝ) → (ι → ℝ)}
    {u : ParS ι ℝ Ω} {x : SProcV ι Ω} (hx : SolvesSV 𝔼 (Gfwd g) u x) (t : ℕ) (i : ι) :
    𝔼.E t (toP x (t + 1) i) = fun ω => g (x (t, ω)) i := by
  have h := hx.2 t i
  have hf : (fun ω => Gfwd g (ptS (u, x) (t, ω)) i) =
      toP x (t + 1) i - fun ω => g (x (t, ω)) i := rfl
  rw [hf, map_sub, known_vec hcl (fun j => hx.1 t j) (fun v => g v i)] at h
  exact sub_eq_zero.mp h

/-! ### The supremum argument on annuli -/

/-- Woodford (2003), App. A.3, p. 634 (tool): **the push argument on annuli.** A family bounded
by `r` is zero if, whenever `B ≤ r` bounds it, every member in the annulus `[B/2, B]` is in fact
at most `B − δ` for some `δ > 0` (apply it at the supremum). -/
theorem eq_zero_of_annulus {J : Type*} (a : J → ℝ) {r : ℝ} (hb : ∀ j, |a j| ≤ r)
    (h : ∀ B, 0 < B → B ≤ r → (∀ j, |a j| ≤ B) →
      ∃ δ > 0, ∀ j, B / 2 ≤ |a j| → |a j| ≤ B - δ) (j : J) : a j = 0 := by
  by_contra hne
  have hpos : 0 < |a j| := abs_pos.mpr hne
  have hbdd : BddAbove (Set.range fun k => |a k|) := ⟨r, by rintro _ ⟨k, rfl⟩; exact hb k⟩
  set S := ⨆ k, |a k| with hS
  have hle : ∀ k, |a k| ≤ S := fun k => le_ciSup hbdd k
  have hSpos : 0 < S := hpos.trans_le (hle j)
  have : Nonempty J := ⟨j⟩
  have hSr : S ≤ r := ciSup_le hb
  obtain ⟨δ, hδ, hδP⟩ := h S hSpos hSr hle
  have hm := lt_min (half_pos hSpos) hδ
  obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup (show S - min (S / 2) δ < S by linarith)
  have h1 : S / 2 ≤ |a k| := by have := min_le_left (S / 2) δ; linarith
  have h2 := hδP k h1
  have := min_le_right (S / 2) δ
  linarith

/-- Woodford (2003), App. A.3, p. 634: `g` is **repelling on annuli up to `r`**: on every annulus
`B/2 ≤ ‖v‖ ≤ B` with `0 < B ≤ r`, `‖g v‖ ≥ ‖v‖ + δ` for some `δ > 0` (sup norm). -/
def RepelAnn (g : (ι → ℝ) → (ι → ℝ)) (r : ℝ) : Prop :=
  ∀ B, 0 < B → B ≤ r → ∃ δ > 0, ∀ v : ι → ℝ, B / 2 ≤ ‖v‖ → ‖v‖ ≤ B → ‖v‖ + δ ≤ ‖g v‖

/-- Woodford (2003), App. A.3, p. 634 (tool): a bounded process is zero once all its values have
norm zero. -/
theorem eq_zero_of_norm (x : SProcV ι Ω) (h : ∀ p, ‖x p‖ = 0) : x = 0 := by
  refine lp.ext (funext fun p => ?_)
  rw [lp.coeFn_zero, Pi.zero_apply]
  exact norm_eq_zero.mp (h p)

/-- **No sunspots, `n` dimensions: a map repelling on annuli** (Woodford (2003), App. A.3,
pp. 632–634): if `g` is repelling on annuli up to `r`, then under informational closure every
bounded adapted equilibrium of `E_t[x_{t+1} − g(x_t)] = 0` within `r` of the steady state is the
steady state: `‖g(x_t)‖ = ‖E_t x_{t+1}‖ ≤ sup ‖x‖` pushes the supremum
down. -/
theorem unique_of_repelAnn (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {g : (ι → ℝ) → (ι → ℝ)} {r : ℝ} (hg : RepelAnn g r) {u : ParS ι ℝ Ω} {x : SProcV ι Ω}
    (hx : SolvesSV 𝔼 (Gfwd g) u x) (hxr : ‖x‖ ≤ r) : x = 0 := by
  have hb : ∀ p : ℕ × Ω, |‖x p‖| ≤ r := fun p => by
    rw [abs_norm]
    exact (LocalIFTStochastic.norm_apply_le x p).trans hxr
  refine eq_zero_of_norm x fun p => eq_zero_of_annulus (fun p : ℕ × Ω => ‖x p‖) hb
    (fun B hB hBr hall => ?_) p
  obtain ⟨δ, hδ, hδP⟩ := hg B hB hBr
  refine ⟨δ, hδ, fun q hq => ?_⟩
  obtain ⟨t, ω⟩ := q
  simp only [abs_norm] at hq hall ⊢
  have hgB : ‖g (x (t, ω))‖ ≤ B := by
    refine (pi_norm_le_iff_of_nonneg hB.le).mpr fun i => ?_
    have hE := congrFun (fwd_E hcl hx t i) ω
    rw [Real.norm_eq_abs, ← hE]
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    change |x (t + 1, ω') i| ≤ B
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ i).trans (hall (t + 1, ω'))
  have := hδP _ hq (hall (t, ω))
  linarith

/-- Woodford (2003), App. A.3, pp. 632–634: if `g` is repelling on annuli at every scale, the
steady state is the **only** bounded adapted equilibrium under informational closure (global
uniqueness). -/
theorem unique_of_repelAnn_global (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼)
    {g : (ι → ℝ) → (ι → ℝ)} (hg : ∀ r, RepelAnn g r) {u : ParS ι ℝ Ω} {x : SProcV ι Ω}
    (hx : SolvesSV 𝔼 (Gfwd g) u x) : x = 0 :=
  unique_of_repelAnn hcl (hg ‖x‖) hx le_rfl

/-! ### The coin tree: dates from 2 on are deterministic -/

/-- Woodford (2003), App. A.3, p. 634 (tool): on the core coin tree both flips are known from
date `2` on, so `E_{t+2}` is the identity. -/
theorem coin_E_late (t : ℕ) (y : Bool × Bool → ℝ) : coinSystem.E (t + 2) y = y := by
  funext ω
  rw [coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h => ?_
  change Setoid.ker (ExpectationsFiniteTree.coinObs (t + 2)) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [ExpectationsFiniteTree.coinObs, Prod.mk.injEq] at h
  have h1 : ω'.1 = ω.1 := by
    have := h.1
    simpa [show 1 ≤ t + 2 by omega] using this
  have h2 : ω'.2 = ω.2 := by
    have := h.2
    simpa [show 2 ≤ t + 2 by omega] using this
  rw [Prod.ext h1 h2]

/-- Woodford (2003), App. A.3, p. 634 (tool): on the coin tree, from date `2` on an equilibrium
of the forward system follows `x_{t+1} = g(x_t)` state by state. -/
theorem coin_step_late {g : (ι → ℝ) → (ι → ℝ)} {u : ParS ι ℝ (Bool × Bool)}
    {x : SProcV ι (Bool × Bool)} (hx : SolvesSV coinSystem (Gfwd g) u x) (s : ℕ)
    (ω : Bool × Bool) : x (s + 3, ω) = g (x (s + 2, ω)) := by
  funext i
  have h := hx.2 (s + 2) i
  rw [coin_E_late] at h
  have := congrFun h ω
  change x (s + 2 + 1, ω) i - g (x (s + 2, ω)) i = 0 at this
  exact sub_eq_zero.mp this

/-- **The coin tree with a two-step repelling map** (Woodford (2003), App. A.3, pp. 632–634): if
`g ∘ g` is repelling on annuli up to `r` and `g` vanishes only at `0` within `r`, every
equilibrium of `E_t[x_{t+1} − g(x_t)] = 0` on the coin tree within `r` of the steady state is
**zero at date 1** (and from date 2 on): from date 2 the path is deterministic and the push
argument applies to `g ∘ g`; then `g(x_1) = E_1 x_2 = 0`. -/
theorem coin_eq_zero_of_two_step {g : (ι → ℝ) → (ι → ℝ)} {r : ℝ} (hG : RepelAnn (g ∘ g) r)
    (hz : ∀ v : ι → ℝ, ‖v‖ ≤ r → g v = 0 → v = 0) {u : ParS ι ℝ (Bool × Bool)}
    {x : SProcV ι (Bool × Bool)} (hx : SolvesSV coinSystem (Gfwd g) u x) (hxr : ‖x‖ ≤ r)
    (ω : Bool × Bool) : x (1, ω) = 0 ∧ ∀ s, x (s + 2, ω) = 0 := by
  have hlate : ∀ s ω', x (s + 2, ω') = 0 := by
    intro s ω'
    have h0 := eq_zero_of_annulus (fun p : ℕ × (Bool × Bool) => ‖x (p.1 + 2, p.2)‖) (r := r)
      (fun p => by rw [abs_norm]; exact (LocalIFTStochastic.norm_apply_le x _).trans hxr)
      (fun B hB hBr hall => ?_) (s, ω')
    · exact norm_eq_zero.mp h0
    obtain ⟨δ, hδ, hδP⟩ := hG B hB hBr
    refine ⟨δ, hδ, fun q hq => ?_⟩
    obtain ⟨t, ω₁⟩ := q
    simp only [abs_norm] at hq hall ⊢
    have e : x (t + 2 + 2, ω₁) = (g ∘ g) (x (t + 2, ω₁)) := by
      rw [Function.comp_apply, ← coin_step_late hx t ω₁, ← coin_step_late hx (t + 1) ω₁]
    have hb := hall (t + 2, ω₁)
    rw [e] at hb
    have := hδP _ hq (hall (t, ω₁))
    linarith
  refine ⟨?_, fun s => hlate s ω⟩
  have hcl : LocalIFTStochastic.Ops.InfoClosed coinSystem :=
    LocalIFTStochastic.finiteTree_infoClosed _
  have hg0 : g (x (1, ω)) = 0 := by
    funext i
    have h := hx.2 1 i
    have hf : (fun ω' => Gfwd g (ptS (u, x) (1, ω')) i) =
        toP x 2 i - fun ω' => g (x (1, ω')) i := rfl
    have h2 : toP x 2 i = 0 := funext fun ω' => by
      change x (0 + 2, ω') i = 0
      rw [hlate 0 ω']
      rfl
    rw [hf, h2, zero_sub, map_neg, known_vec hcl (fun j => hx.1 1 j) (fun v => g v i)] at h
    have := congrFun h ω
    simp only [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at this
    exact this
  exact hz _ ((LocalIFTStochastic.norm_apply_le x _).trans hxr) hg0

/-- **No random sunspots on the coin tree with a two-step repelling map** (Woodford (2003),
App. A.3, pp. 632–634): under the hypotheses of `coin_eq_zero_of_two_step` (with `r > 0`), there
is a scale below which no equilibrium on the coin tree has a date-1 value differing across the
first flip. -/
theorem no_coin_sunspot_of_two_step {g : (ι → ℝ) → (ι → ℝ)} {r : ℝ} (hr : 0 < r)
    (hG : RepelAnn (g ∘ g) r) (hz : ∀ v : ι → ℝ, ‖v‖ ≤ r → g v = 0 → v = 0) :
    ¬ ∀ ε > 0, ∃ x : SProcV ι (Bool × Bool), SolvesSV coinSystem (Gfwd g) 0 x ∧ ‖x‖ ≤ ε ∧
      x (1, (true, true)) ≠ x (1, (false, true)) := by
  intro h
  obtain ⟨x, hx, hxn, hne⟩ := h r hr
  rw [(coin_eq_zero_of_two_step hG hz hx hxn (true, true)).1,
    (coin_eq_zero_of_two_step hG hz hx hxn (false, true)).1] at hne
  exact hne rfl

/-! ### Constructing random sunspots on the coin tree -/

/-- Woodford (2003), App. A.3, p. 634 (tool): the coin-tree process with `x_0 = c` and
`x_{t+1} = y_b(t)` after first flip `b`. -/
noncomputable def pathProc (c : ι → ℝ) (y : Bool → ℕ → ι → ℝ) {M : ℝ}
    (hM : ∀ b t, ‖y b t‖ ≤ M) : SProcV ι (Bool × Bool) :=
  LocalIFTStochastic.mkB (fun p => lagV c (y p.2.1) p.1) ⟨max ‖c‖ M, fun p => by
    obtain ⟨t, ω⟩ := p
    cases t with
    | zero => exact le_max_left _ _
    | succ t => exact (hM _ t).trans (le_max_right _ _)⟩

/-- Woodford (2003), App. A.3, p. 634 (tool): the path process is within `max(‖c‖, M)` of the
steady state. -/
theorem norm_pathProc_le {c : ι → ℝ} {y : Bool → ℕ → ι → ℝ} {M : ℝ}
    (hM : ∀ b t, ‖y b t‖ ≤ M) : ‖pathProc c y hM‖ ≤ max ‖c‖ M := by
  refine LocalIFTStochastic.norm_le_of_forall ((norm_nonneg c).trans (le_max_left _ _))
    fun p => ?_
  obtain ⟨t, ω⟩ := p
  cases t with
  | zero => exact le_max_left _ _
  | succ t => exact (hM _ t).trans (le_max_right _ _)

/-- Woodford (2003), App. A.3, p. 634 (tool): **the path process is an equilibrium** of the
forward system on the coin tree when each branch follows `y_{t+1} = g(y_t)` and the two date-1
values average to `g(c)`. -/
theorem solvesSV_pathProc {g : (ι → ℝ) → (ι → ℝ)} {c : ι → ℝ} {y : Bool → ℕ → ι → ℝ} {M : ℝ}
    (hM : ∀ b t, ‖y b t‖ ≤ M) (h0 : g c = (1 / 2 : ℝ) • (y true 0 + y false 0))
    (hstep : ∀ b t, y b (t + 1) = g (y b t)) :
    SolvesSV coinSystem (Gfwd g) 0 (pathProc c y hM) := by
  refine ⟨fun t i => ?_, fun t i => ?_⟩
  · cases t with
    | zero =>
      change coinSystem.E 0 (fun _ => c i) = fun _ => c i
      exact coinSystem.const 0 _
    | succ t =>
      change coinSystem.E (t + 1) (fun ω => y ω.1 t i) = fun ω => y ω.1 t i
      exact LocalIFTStochasticModels.coin_known_fst t (fun b => y b t i)
  · cases t with
    | zero =>
      have hf : (fun ω => Gfwd g (ptS ((0 : ParS ι ℝ (Bool × Bool)), pathProc c y hM) (0, ω)) i) =
          fun ω => y ω.1 0 i - g c i := rfl
      rw [hf]
      funext ω
      rw [LocalIFTStochasticModels.coin_E0]
      have e := congrFun h0 i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e
      simp only [Pi.zero_apply]
      rw [e]
      ring
    | succ t =>
      have hf : (fun ω => Gfwd g (ptS ((0 : ParS ι ℝ (Bool × Bool)), pathProc c y hM)
          (t + 1, ω)) i) = 0 := by
        funext ω
        change y ω.1 (t + 1) i - g (y ω.1 t) i = 0
        rw [hstep]
        exact sub_self _
      rw [hf]
      exact map_zero _

/-- Woodford (2003), App. A.3, p. 634 (tool): the orbit `v, g(v), g(g(v)), …`. -/
def orb (g : (ι → ℝ) → (ι → ℝ)) (v : ι → ℝ) : ℕ → ι → ℝ
  | 0 => v
  | t + 1 => g (orb g v t)

/-- Woodford (2003), App. A.3, p. 634 (tool): **orbits from a two-step invariant set stay
small**: if `g ∘ g` maps `A` into itself without increasing the norm and `‖g v‖ ≤ L‖v‖` on `A`
(`L ≥ 1`), the orbit from `v ∈ A` stays within `L‖v‖`. -/
theorem norm_orb_le {g : (ι → ℝ) → (ι → ℝ)} {A : Set (ι → ℝ)} {L : ℝ} (hL : 1 ≤ L)
    (hA : ∀ v ∈ A, g (g v) ∈ A ∧ ‖g (g v)‖ ≤ ‖v‖) (hgL : ∀ v ∈ A, ‖g v‖ ≤ L * ‖v‖)
    {v : ι → ℝ} (hv : v ∈ A) (t : ℕ) : ‖orb g v t‖ ≤ L * ‖v‖ := by
  have heven : ∀ s, orb g v (2 * s) ∈ A ∧ ‖orb g v (2 * s)‖ ≤ ‖v‖ := by
    intro s
    induction s with
    | zero => exact ⟨hv, le_rfl⟩
    | succ s ih =>
      have e : orb g v (2 * (s + 1)) = g (g (orb g v (2 * s))) := by
        rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring]
        rfl
      rw [e]
      exact ⟨(hA _ ih.1).1, (hA _ ih.1).2.trans ih.2⟩
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  obtain ⟨s, hs | hs⟩ := Nat.even_or_odd' t
  · rw [hs]
    calc ‖orb g v (2 * s)‖ ≤ ‖v‖ := (heven s).2
      _ ≤ L * ‖v‖ := le_mul_of_one_le_left hv0 hL
  · rw [hs]
    change ‖g (orb g v (2 * s))‖ ≤ L * ‖v‖
    exact (hgL _ (heven s).1).trans (mul_le_mul_of_nonneg_left (heven s).2 (by linarith))

omit [Fintype ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): orbits follow `g`. -/
theorem orb_succ (g : (ι → ℝ) → (ι → ℝ)) (v : ι → ℝ) (t : ℕ) :
    orb g v (t + 1) = g (orb g v t) := rfl

/-- **Random sunspots of `n`-dimensional forward systems from a two-step invariant set**
(Woodford (2003), App. A.3, pp. 632–634): if `g ∘ g` maps `A` into itself without increasing the
norm, `‖g v‖ ≤ L‖v‖` on `A` (`L ≥ 1`), and two distinct points `y₁, y₂ ∈ A` average to `g(c)`,
then on the core coin tree the forward system `E_t[x_{t+1} − g(x_t)] = 0` (no disturbances,
`x_{−1} = 0`) has a bounded adapted equilibrium within `max(‖c‖, L max(‖y₁‖, ‖y₂‖))` of the
steady state whose date-1 value differs across the first flip. -/
theorem coin_sunspot_of_pair {g : (ι → ℝ) → (ι → ℝ)} {A : Set (ι → ℝ)} {L : ℝ} (hL : 1 ≤ L)
    (hA : ∀ v ∈ A, g (g v) ∈ A ∧ ‖g (g v)‖ ≤ ‖v‖) (hgL : ∀ v ∈ A, ‖g v‖ ≤ L * ‖v‖)
    {c y₁ y₂ : ι → ℝ} (h₁ : y₁ ∈ A) (h₂ : y₂ ∈ A) (hne : y₁ ≠ y₂)
    (hc : g c = (1 / 2 : ℝ) • (y₁ + y₂)) :
    ∃ x : SProcV ι (Bool × Bool), SolvesSV coinSystem (Gfwd g) 0 x ∧
      ‖x‖ ≤ max ‖c‖ (L * max ‖y₁‖ ‖y₂‖) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  set y : Bool → ℕ → ι → ℝ := fun b => orb g (if b then y₁ else y₂) with hy
  have hM : ∀ b t, ‖y b t‖ ≤ L * max ‖y₁‖ ‖y₂‖ := by
    intro b t
    cases b
    · exact (norm_orb_le hL hA hgL h₂ t).trans
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith))
    · exact (norm_orb_le hL hA hgL h₁ t).trans
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
  refine ⟨pathProc c y hM, solvesSV_pathProc hM ?_ (fun b t => orb_succ g _ t),
    norm_pathProc_le hM, ?_⟩
  · simpa [hy, orb] using hc
  · change orb g y₁ 0 ≠ orb g y₂ 0
    exact hne

end Woodford.PriceLevelDetermination.TidyR6ForwardSunspots
