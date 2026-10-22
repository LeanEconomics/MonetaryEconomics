/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergNewton
import StabilizationWelfare.NonlinearNKMarkovAdapted

/-!
# Markov and sequence-space equilibria of the exact Rotemberg model

Woodford (2003), *Interest and Prices*, Chapter 3, fn. 44 (p. 188, the Rotemberg model),
Chapter 4, §2.2 (Proposition 4.3 and (2.7), p. 254), Chapter 6, §1 (pp. 383–392) and Appendix A.3
(pp. 631–635), applied to the exact Rotemberg model of `NonlinearRotemberg`.

## Main results

* `LG_eq`: the abstract linearised operator of `NonlinearRotembergNewton` is the Rotemberg `Lop`.
* **`markov_equilibrium_general`**: under the Taylor principle in the Rotemberg slope there are
  `r, δ > 0`, depending only on the parameters, such that on EVERY state space with EVERY Markov
  operator and EVERY disturbance pattern with `‖e‖ ≤ δ` there is exactly one Markov equilibrium
  with `‖z‖ ≤ r` (`rot_existence_inv` adds an invariant class).
* **`seq_existence`**, `seq_uniqueness`: for EVERY core `ExpectationSystem` and every bounded
  disturbance process, the exact stochastic conditions have exactly one solution within `r`
  (no Markov structure, no adaptedness assumed for the competitor);
  **`seq_existence_adapted`**: it is adapted when the system is informationally closed (every
  finite event tree, `NonlinearNKMarkovAdapted.finiteTree_infoClosed`).
* **`markov_is_unique_process`**: on a finite chain, the Markov equilibrium is the unique bounded
  process near the steady state.
* **`steadyState_locally_unique`**: the zero-inflation steady state is the only steady state in a
  ball around it.
* **`linear_determinate_iff`**: the linearised Rotemberg model (IS curve and NKPC) is determinate
  on an expectation system iff the Taylor principle holds in the Rotemberg slope; and
  **`lop_injective_iff`**: the linearised operator is injective on every finite Markov chain iff
  the Taylor principle holds.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergMarkov

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov chainOp Stochastic chainOp_isMarkov)
open NonlinearNKMarkovGeneral (seqOp seqOp_isMarkov fwdSol)
open NonlinearNKMarkovLinks (MarkovProp)
open NonlinearNKMarkovAdapted (CC cc_fwdSol cc_Mv cc_lim InfoClosed cellConst_of_known)
open NonlinearRotemberg NonlinearRotembergNewton

variable {p : Par} {X : Type*}

/-- Woodford (2003), App. A.3: the linearised operator of the abstract residual for the Rotemberg
maps is `Lop` (`DQ0`, `DN0` are the exact derivatives). -/
theorem LG_eq (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v : X → Fin 3 → ℝ) :
    LG (Qmap p) (Nmap p) M v = Lop p M v := by
  funext x
  simp only [LG, Lop, fderiv_Qmap_inr, fderiv_Nmap_inr]

/-- Woodford (2003), App. A.3: `linSol` is additive in differences on bounded functions. -/
theorem linSol_sub (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {r r' : X → Fin 3 → ℝ} {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') (hr : ∀ x, ‖r x‖ ≤ a)
    (hr' : ∀ x, ‖r' x‖ ≤ a') :
    linSol p M (fun x => r x - r' x) = fun x => linSol p M r x - linSol p M r' x := by
  have hd : ∀ x, ‖r x - r' x‖ ≤ a + a' := fun x => (norm_sub_le _ _).trans (add_le_add (hr x)
    (hr' x))
  obtain ⟨hC1, hL1⟩ := linSol_spec hp hM (add_nonneg ha ha') hd
  obtain ⟨hC2, hL2⟩ := linSol_spec hp hM ha hr
  obtain ⟨hC3, hL3⟩ := linSol_spec hp hM ha' hr'
  have h0 : (fun x => linSol p M (fun x => r x - r' x) x -
      (linSol p M r x - linSol p M r' x)) = 0 := by
    refine Lop_injective hp hM (V := KL p * (a + a') + (KL p * a + KL p * a'))
      (fun x => (norm_sub_le _ _).trans
      (add_le_add (hC1 x) ((norm_sub_le _ _).trans (add_le_add (hC2 x) (hC3 x))))) ?_
    rw [Lop_sub, hL1, Lop_sub, hL2, hL3]; funext x; simp
  funext x
  exact sub_eq_zero.1 (congrFun h0 x)

/-- Woodford (2003), App. A.3: the right-inverse hypothesis of `newton_exist` for `linSol`. -/
theorem linSol_right (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) :
    ∀ ρ a, 0 ≤ a → (∀ x, ‖ρ x‖ ≤ a) →
      (∀ x, ‖linSol p M ρ x‖ ≤ KL p * a) ∧ LG (Qmap p) (Nmap p) M (linSol p M ρ) = ρ :=
  fun ρ a ha hρ => by
    obtain ⟨h1, h2⟩ := linSol_spec hp hM ha hρ
    exact ⟨h1, by rw [LG_eq]; exact h2⟩

/-- Woodford (2003), App. A.3: the left-inverse hypothesis of `newton_exist` for `linSol`, on all
bounded functions. -/
theorem linSol_left (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M) :
    ∀ v w : X → Fin 3 → ℝ, True → True → ∀ D, (∀ x, ‖v x - w x‖ ≤ D) →
      linSol p M (LG (Qmap p) (Nmap p) M (fun x => v x - w x)) = fun x => v x - w x := by
  intro v w _ _ D hD
  have hD0 : ∀ x, 0 ≤ D := fun x => (norm_nonneg _).trans (hD x)
  rw [LG_eq]
  by_cases hX : Nonempty X
  · obtain ⟨x0⟩ := hX
    have hb := LG_bounded (Q := Qmap p) (N := Nmap p) hM (hD0 x0) hD
    rw [LG_eq] at hb
    exact linSol_Lop hp hM hb hD
  · funext x; exact absurd ⟨x⟩ hX

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**existence with an invariant class and
uniqueness, uniform over state spaces**): under the Taylor principle there are `r, δ > 0` such
that on every state space with every Markov operator and every disturbance with `‖e‖ ≤ δ`:
(i) for every class `S` containing `0`, invariant under the Newton step and closed under pointwise
limits, there is a Markov equilibrium in `S` within `r`; (ii) any two Markov equilibria within `r`
coincide. -/
theorem rot_existence_inv (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ e : X → Fin 3 → ℝ, (∀ x, ‖e x‖ ≤ δ) →
      (∀ (S : (X → Fin 3 → ℝ) → Prop), S 0 →
        (∀ z, S z → (∀ x, ‖z x‖ ≤ r) →
          S (fun x => z x - linSol p M (PhiG (Qmap p) (Nmap p) M e z) x)) →
        (∀ (zs : ℕ → X → Fin 3 → ℝ) (z : X → Fin 3 → ℝ), (∀ k, S (zs k)) →
          (∀ x, Tendsto (fun k => zs k x) atTop (𝓝 (z x))) → S z) →
        ∃ z, S z ∧ (∀ x, ‖z x‖ ≤ r) ∧ PhiG (Qmap p) (Nmap p) M e z = 0) ∧
      ∀ z z' : X → Fin 3 → ℝ, (∀ x, ‖z x‖ ≤ r) → (∀ x, ‖z' x‖ ≤ r) →
        PhiG (Qmap p) (Nmap p) M e z = 0 → PhiG (Qmap p) (Nmap p) M e z' = 0 → z = z' := by
  have hK := KL_pos hp.basic
  obtain ⟨ρ, hρ, hu⟩ := newton_unique (contDiff_Qmap (p := p) (n := 1))
    (contDiff_Nmap (p := p) (n := 1)) hK
  obtain ⟨r0, hr0, hex⟩ := newton_exist (contDiff_Qmap (p := p) (n := 1))
    (contDiff_Nmap (p := p) (n := 1)) steadyState_zero hK
  obtain ⟨δ1, hδ1, hex1⟩ := hex (min r0 ρ) (lt_min hr0 hρ) (min_le_left _ _)
  refine ⟨min r0 ρ, lt_min hr0 hρ, min δ1 ρ, lt_min hδ1 hρ, fun X M hM e he => ⟨?_, ?_⟩⟩
  · intro S hS0 hSinv hSlim
    exact hex1 X M hM (linSol p M) (linSol_right hp hM)
      (fun ρ ρ' a a' ha ha' h1 h2 => linSol_sub hp hM ha ha' h1 h2) S
      (fun v w _ _ D hD => linSol_left hp hM v w trivial trivial D hD) e
      (fun x => (he x).trans (min_le_left _ _)) hS0 hSinv hSlim
  · intro z z' hz hz' hE hE'
    exact hu X M hM (fun _ => True)
      (apriori_of_linv (linSol_right hp hM) (linSol_left hp hM)) e z z'
      (fun x => (he x).trans (min_le_right _ _)) trivial trivial
      (fun x => (hz x).trans (min_le_right _ _)) (fun x => (hz' x).trans (min_le_right _ _))
      hE hE'

/-- Woodford (2003), Ch. 6, §1, App. A.3 and Proposition 4.3 (**EXISTENCE AND LOCAL UNIQUENESS OF
A MARKOV EQUILIBRIUM OF THE EXACT ROTEMBERG MODEL ON A GENERAL SHOCK SPACE**). Under the Taylor
principle in the Rotemberg slope there are `r, δ > 0`, depending ONLY on the parameters, such
that for every state space `X`, every Markov operator `M` and every disturbance pattern with
`‖e(x)‖ ≤ δ` there is exactly one Markov equilibrium `z : X → ℝ³` (`ŷ, π, ĉ`) with
`‖z(x)‖ ≤ r`. -/
theorem markov_equilibrium_general (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ e : X → Fin 3 → ℝ, (∀ x, ‖e x‖ ≤ δ) →
        ∃ z : X → Fin 3 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ PhiG (Qmap p) (Nmap p) M e z = 0) ∧
          ∀ z' : X → Fin 3 → ℝ, (∀ x, ‖z' x‖ ≤ r) → PhiG (Qmap p) (Nmap p) M e z' = 0 →
            z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := rot_existence_inv hp
  refine ⟨r, hr, δ, hδ, fun X M hM e he => ?_⟩
  obtain ⟨hex, hu⟩ := h X M hM e he
  obtain ⟨z, -, hzB, hz⟩ := hex (fun _ => True) trivial (fun _ _ _ => trivial)
    (fun _ _ _ _ => trivial)
  exact ⟨z, ⟨hzB, hz⟩, fun z' hz'B hz' => hu z' z hz'B hzB hz' hz⟩

/-- Woodford (2003), Ch. 3 §2 with Rotemberg pricing (**local uniqueness of the steady state**):
there is `r > 0` such that every steady state `x` (constant inflation, output and consumption, no
disturbances) with `‖x‖ ≤ r` is the zero-inflation steady state `x = 0`. -/
theorem steadyState_locally_unique (hp : p.Std) :
    ∃ r > 0, ∀ x : Fin 3 → ℝ, ‖x‖ ≤ r → Qmap p (0, x) + Nmap p (0, x) = 0 → x = 0 := by
  obtain ⟨r, hr, δ, hδ, h⟩ := rot_existence_inv hp
  refine ⟨r, hr, fun x hx hss => ?_⟩
  have hM : IsMarkov (LinearMap.id : (Unit → ℝ) →ₗ[ℝ] (Unit → ℝ)) :=
    ⟨rfl, fun h C hC u => hC u⟩
  obtain ⟨-, hu⟩ := h Unit LinearMap.id hM (fun _ => 0) (fun _ => by simp [hδ.le])
  have hPhi : ∀ y : Fin 3 → ℝ, PhiG (Qmap p) (Nmap p) LinearMap.id
      (fun _ : Unit => (0 : Fin 3 → ℝ)) (fun _ : Unit => y) =
      fun _ => Qmap p (0, y) + Nmap p (0, y) := fun y => by
    funext u i; rfl
  have := hu (fun _ => x) (fun _ => 0) (fun _ => hx) (fun _ => by simp [hr.le])
    (by rw [hPhi, hss]; rfl) (by rw [hPhi, steadyState_zero]; rfl)
  exact congrFun this ()

/-! ## Sequence space: every expectation system -/

/-- Woodford (2003), (A.11) with Rotemberg pricing (**the exact stochastic equilibrium conditions
in sequence space**): `Q(e_t, z_t) + E_t[N(e_{t+1}, z_{t+1})] = 0` at every date and state (the
Euler equation with the rule, the exact pricing condition, the resource constraint). -/
def SeqEqm {Ω : Type*} (p : Par) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 3 → ℝ)
    (z : ℕ → Ω → Fin 3 → ℝ) : Prop :=
  ∀ t ω, Qmap p (e t ω, z t ω) +
    (fun i => 𝔼.E t (fun ω' => Nmap p (e (t + 1) ω', z (t + 1) ω') i) ω) = 0

/-- The sequence-space conditions are the Markov conditions on `ℕ × Ω` with `seqOp`. -/
theorem seqEqm_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 3 → ℝ)
    (z : ℕ → Ω → Fin 3 → ℝ) :
    SeqEqm p 𝔼 e z ↔
      PhiG (Qmap p) (Nmap p) (seqOp 𝔼) (fun q => e q.1 q.2) (fun q => z q.1 q.2) = 0 := by
  constructor
  · intro h
    funext q
    exact h q.1 q.2
  · intro h t ω
    exact congrFun h (t, ω)

/-- Woodford (2003), App. A.3 and Proposition 4.3, Rotemberg pricing (**SEQUENCE-SPACE
EXISTENCE AND UNIQUENESS for every expectation system**): there are `r, δ > 0` such that for every
expectation system and every disturbance process with `‖e_t(ω)‖ ≤ δ`, the exact stochastic
conditions have a solution within `r`, and it is the only one within `r` (no Markov property and
no adaptedness are assumed of the competitor). -/
theorem seq_existence (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 3 → ℝ),
      (∀ t ω, ‖e t ω‖ ≤ δ) → ∃ z : ℕ → Ω → Fin 3 → ℝ, ((∀ t ω, ‖z t ω‖ ≤ r) ∧
        SeqEqm p 𝔼 e z) ∧ ∀ z' : ℕ → Ω → Fin 3 → ℝ, (∀ t ω, ‖z' t ω‖ ≤ r) →
          SeqEqm p 𝔼 e z' → z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := markov_equilibrium_general hp
  refine ⟨r, hr, δ, hδ, fun Ω 𝔼 e he => ?_⟩
  obtain ⟨z, ⟨hzB, hz⟩, hu⟩ := h (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼) (fun q => e q.1 q.2)
    (fun q => he q.1 q.2)
  refine ⟨fun t ω => z (t, ω), ⟨fun t ω => hzB (t, ω), (seqEqm_iff 𝔼 e _).2 hz⟩,
    fun z' hz'B hz' => ?_⟩
  have := hu (fun q => z' q.1 q.2) (fun q => hz'B q.1 q.2) ((seqEqm_iff 𝔼 e z').1 hz')
  funext t ω; exact congrFun this (t, ω)

/-- Woodford (2003), App. A.3, Rotemberg pricing (**sequence-space uniqueness among ALL bounded
processes**): two solutions within `r` of the exact stochastic conditions coincide. -/
theorem seq_uniqueness (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 3 → ℝ)
      (z z' : ℕ → Ω → Fin 3 → ℝ), (∀ t ω, ‖e t ω‖ ≤ δ) → (∀ t ω, ‖z t ω‖ ≤ r) →
        (∀ t ω, ‖z' t ω‖ ≤ r) → SeqEqm p 𝔼 e z → SeqEqm p 𝔼 e z' → z = z' := by
  obtain ⟨r, hr, δ, hδ, h⟩ := seq_existence hp
  refine ⟨r, hr, δ, hδ, fun Ω 𝔼 e z z' he hz hz' hE hE' => ?_⟩
  obtain ⟨w, -, hu⟩ := h Ω 𝔼 e he
  rw [hu z hz hE, hu z' hz' hE']

/-! ## Adaptedness -/

/-- Woodford (2003), App. A.3: the inverse of the linearised operator preserves cell-constancy. -/
theorem cc_linSol {Ω : Type*} (𝔼 : ExpectationSystem Ω) {r : ℕ × Ω → Fin 3 → ℝ}
    (hr : CC 𝔼 r) : CC 𝔼 (linSol p (seqOp 𝔼) r) := by
  have hb : CC 𝔼 (bR p r) := fun t ω ω' h => by
    simp only [bR, gR0, gR1, hr t ω ω' h]
  have hu : CC 𝔼 (uR p (seqOp 𝔼) r) := cc_fwdSol 𝔼 _ hb
  intro t ω ω' h
  simp only [linSol, hr t ω ω' h, hu t ω ω' h]

/-- Woodford (2003), (A.11): the residual preserves cell-constancy for cell-constant
disturbances. -/
theorem cc_PhiG {Ω : Type*} (𝔼 : ExpectationSystem Ω) {e : ℕ × Ω → Fin 3 → ℝ} (he : CC 𝔼 e)
    {z : ℕ × Ω → Fin 3 → ℝ} (hz : CC 𝔼 z) :
    CC 𝔼 (PhiG (Qmap p) (Nmap p) (seqOp 𝔼) e z) := fun t ω ω' h => by
  simp only [PhiG]
  rw [he t ω ω' h, hz t ω ω' h, cc_Mv 𝔼 _ t ω ω' h]

/-- Woodford (2003), App. A.3, p. 633, Rotemberg pricing (**the sequence-space equilibrium is
ADAPTED**): if the expectation system is informationally closed (e.g. every finite event tree) and
the disturbances are known at each date, the unique solution within `r` satisfies
`E_t z_t = z_t`. -/
theorem seq_existence_adapted (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω), InfoClosed 𝔼 →
      ∀ e : ℕ → Ω → Fin 3 → ℝ, (∀ t ω, ‖e t ω‖ ≤ δ) →
        (∀ t (i : Fin 3), 𝔼.E t (fun ω => e t ω i) = fun ω => e t ω i) →
        ∃ z : ℕ → Ω → Fin 3 → ℝ, (((∀ t ω, ‖z t ω‖ ≤ r) ∧ SeqEqm p 𝔼 e z) ∧
          ∀ t (i : Fin 3), 𝔼.E t (fun ω => z t ω i) = fun ω => z t ω i) ∧
          ∀ z' : ℕ → Ω → Fin 3 → ℝ, (∀ t ω, ‖z' t ω‖ ≤ r) → SeqEqm p 𝔼 e z' → z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := rot_existence_inv hp
  refine ⟨r, hr, δ, hδ, fun Ω 𝔼 hcl e he hek => ?_⟩
  have hce : CC 𝔼 (fun q : ℕ × Ω => e q.1 q.2) := fun t ω ω' hi => by
    funext i; exact cellConst_of_known 𝔼 (hek t i) ω ω' hi
  obtain ⟨hex, hu⟩ := h (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼) (fun q => e q.1 q.2)
    (fun q => he q.1 q.2)
  obtain ⟨z, hzA, hzB, hz⟩ := hex (CC 𝔼) (fun _ _ _ _ => rfl)
    (fun z hz _ => fun t ω ω' h => by
      have h1 := cc_linSol (p := p) 𝔼 (cc_PhiG (p := p) 𝔼 hce hz) t ω ω' h
      simp only [hz t ω ω' h, h1])
    (fun zs z hzs hlim => cc_lim 𝔼 hzs hlim)
  have hzS : SeqEqm p 𝔼 e (fun t ω => z (t, ω)) := (seqEqm_iff 𝔼 e _).2 hz
  refine ⟨fun t ω => z (t, ω), ⟨⟨fun t ω => hzB (t, ω), hzS⟩, fun t i => hcl t _
    fun ω ω' hi => by simp only [hzA t ω ω' hi]⟩, fun z' hz'B hz' => ?_⟩
  have := hu (fun q => z' q.1 q.2) z (fun q => hz'B q.1 q.2) hzB ((seqEqm_iff 𝔼 e z').1 hz') hz
  funext t ω; exact congrFun this (t, ω)

/-! ## The Markov equilibrium of a finite chain is the unique bounded process -/

variable {S : Type*} [Fintype S]

/-- Woodford (2003), App. A.3: if the expectation system follows a finite chain along `s_t(ω)`
(`MarkovProp`), a Markov equilibrium `w` composed with the chain solves the sequence-space
conditions. -/
theorem markov_is_process {Ω : Type*} (𝔼 : ExpectationSystem Ω) {P : S → S → ℝ}
    (ξ : S → Fin 3 → ℝ) (w : S → Fin 3 → ℝ)
    (hw : PhiG (Qmap p) (Nmap p) (chainOp P) ξ w = 0) (sh : ℕ → Ω → S)
    (hM : MarkovProp 𝔼 P sh) :
    SeqEqm p 𝔼 (fun t ω => ξ (sh t ω)) (fun t ω => w (sh t ω)) := by
  intro t ω
  funext i
  have h := congrFun (congrFun hw (sh t ω)) i
  have hE := congrFun (hM t (fun s' => Nmap p (ξ s', w s') i)) ω
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [hE]
  exact h

/-- Woodford (2003), App. A.3 and Proposition 4.3, Rotemberg pricing (**the Markov equilibrium is
the unique bounded process**): with `r, δ` of `seq_uniqueness`, if the expectation system follows
the chain and `w` is a Markov equilibrium within `r` with disturbances within `δ`, every process
within `r` solving the exact stochastic conditions is `w(s_t(ω))`. -/
theorem markov_is_unique_process (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (S : Type*) [Fintype S] (Ω : Type*) (𝔼 : ExpectationSystem Ω)
      (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) (w : S → Fin 3 → ℝ) (sh : ℕ → Ω → S),
        PhiG (Qmap p) (Nmap p) (chainOp P) ξ w = 0 → MarkovProp 𝔼 P sh →
        (∀ s, ‖ξ s‖ ≤ δ) → (∀ s, ‖w s‖ ≤ r) → ∀ z : ℕ → Ω → Fin 3 → ℝ,
          (∀ t ω, ‖z t ω‖ ≤ r) → SeqEqm p 𝔼 (fun t ω => ξ (sh t ω)) z →
            z = fun t ω => w (sh t ω) := by
  obtain ⟨r, hr, δ, hδ, h⟩ := seq_uniqueness hp
  exact ⟨r, hr, δ, hδ, fun S _ Ω 𝔼 P ξ w sh hw hM he hwB z hzB hz =>
    h Ω 𝔼 _ z _ (fun t ω => he _) hzB (fun t ω => hwB _) hz
      (markov_is_process 𝔼 ξ w hw sh hM)⟩

/-! ## Necessity at the linear level -/

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) with the Rotemberg NKPC (**the linearised model in the
form of the core**): bounded processes `(ĉ, π)` satisfy the IS curve
`(σ + φ_y)ĉ_t + φ_π π_t = σE_tĉ_{t+1} + E_tπ_{t+1} + g₀` and the NKPC
`π_t = κĉ_t + βE_tπ_{t+1} + g₁` iff they solve `x_t = A E_t x_{t+1} + B₀⁻¹g` (`Solves`). -/
theorem lin_system_iff_solves (hp : p.Basic) {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    (g : ℕ → Fin 2 → Ω → ℝ) (x : ℕ → Fin 2 → Ω → ℝ) :
    (∀ t, (p.σ + p.φy) • x t 0 + p.φ • x t 1 =
        p.σ • 𝔼.E t (x (t + 1) 0) + 𝔼.E t (x (t + 1) 1) + g t 0 ∧
      x t 1 = p.κ • x t 0 + p.β • 𝔼.E t (x (t + 1) 1) + g t 1) ↔
    𝔼.Solves (Arot p) (fun t i => ![p.dd⁻¹ • (g t 0 - p.φ • g t 1),
      p.dd⁻¹ • (p.κ • g t 0 + (p.σ + p.φy) • g t 1)] i) x := by
  have hd := hp.dd_pos
  have hdd : p.dd = p.σ + p.φy + p.φ * p.κ := rfl
  constructor
  · intro h t i
    obtain ⟨h0, h1⟩ := h t
    funext ω
    have e0 := congrFun h0 ω
    have e1 := congrFun h1 ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e0 e1
    fin_cases i
    · simp only [Arot, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      field_simp
      rw [hdd]
      linear_combination e0 - p.φ * e1
    · simp only [Arot, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp
      rw [hdd]
      linear_combination p.κ * e0 + (p.σ + p.φy) * e1
  · intro h t
    have h0 := h t 0
    have h1 := h t 1
    refine ⟨funext fun ω => ?_, funext fun ω => ?_⟩
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e0 e1 ⊢
      rw [e0, e1]
      field_simp
      rw [hdd]
      ring
    · have e0 := congrFun h0 ω
      have e1 := congrFun h1 ω
      simp only [Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e0 e1 ⊢
      rw [e0, e1]
      field_simp
      rw [hdd]
      ring

/-- Woodford (2003), Proposition 4.3, p. 254, Rotemberg slope (**linear DETERMINACY IFF the Taylor
principle**): on every nonempty expectation system, the linearised Rotemberg model (IS curve and
NKPC in `(ĉ, π)`, `ŷ = ĉ` to first order) has at most one bounded adapted solution for every
forcing iff `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem linear_determinate_iff (hp : p.Basic) {Ω : Type*} [Nonempty Ω]
    (𝔼 : ExpectationSystem Ω) :
    𝔼.Determinate (Arot p) ↔ 0 < p.κ * (p.φ - 1) + (1 - p.β) * p.φy := by
  rw [ExpectationSystem.determinate_iff, schurStable_Arot_iff hp]

end Woodford.StabilizationWelfare.NonlinearRotembergMarkov
