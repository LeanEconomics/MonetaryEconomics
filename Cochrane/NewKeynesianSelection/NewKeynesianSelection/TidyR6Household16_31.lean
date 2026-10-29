/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6MoneyInUtility
import NewKeynesianSelection.TidyR6Household16_25
import NewKeynesianSelection.SelectionPatches

/-!
# The household problem behind (16.31)

Cochrane (2023), Chapter 16, §16.10.6, p. 393: "The idea is easiest to express with money in the
utility function, so `u(c_t)` becomes `u(c_t, M_t/P_t)`. In equilibrium with a constant endowment
`c_t = y`, the intertemporal first-order condition becomes (16.31)
`1 + i_t = Π_{t+1}u_c(y, M_t/P_t)/(βu_c(y, M_{t+1}/P_{t+1}))` … expressing the money `u_m` vs.
consumption `u_c` first-order condition as `M_t/P_t = L(y, i_t)`".

The money-in-utility household of Chapter 19 (restated in TidyR6HouseholdMoney and
TidyR6MoneyInUtility: complete contingent-claim markets with state prices `Λ_t`, a genuine
probability space, budget constraints holding almost surely) is solved here at the equilibrium
`c_t = y`:

* `bond_1631`: the stochastic (16.31),
  `1/(1 + i_t) = βE_t[(u_c(y, m_{t+1})/u_c(y, m_t))/Π_{t+1}]` almost surely, derived from
  optimality;
* `money_demand_1631`: `u_m/u_c = i_t/(1 + i_t)`, hence `m_t = L(i_t)` for any money-demand
  function `L` that inverts it (`MoneyDemand`);
* on the one-state tree (the book's "perfect-foresight model"): `unit_E`, `unit_bondPrice`,
  `pf_optimal_iff` — consuming the endowment and holding `m_t` is optimal **iff** (16.31) holds
  exactly and `u_m/u_c = i/(1 + i)` at every date (with the normalisation `Λ_0 = u_c(0)`);
  `pf_1632_of_optimal`: with the rule `1 + i_t = Φ(Π_t)/β` and money demand `m_t = L(i_t)`,
  optimisation gives (16.32) `Π_{t+1} = Φ(Π_t)k(Π_{t+1})/k(Π_t)`,
  `k(Π) = u_c(y, L(Φ(Π)/β − 1))` (`SelectionPatches.eq1632_iff`).
-/

namespace Cochrane.NewKeynesianSelection.TidyR6Household16_31

open MeasureTheory ProbabilityTheory Filter Topology TidyR6ExpectationsMeasure
open TidyR6HouseholdMoney TidyR6MoneyInUtility

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), eq. (16.31), p. 393, on a probability space, derived from optimality: if
consuming the constant endowment `y` and holding real balances `m` is optimal (smooth utility,
regular prices, `m` essentially bounded, `u_c(y, m_t) ≠ 0` with bounded reciprocal), then with
`1 + i_t = 1/Q_t` almost surely `1/(1 + i_t) = βE_t[(u_c(y, m_{t+1})/u_c(y, m_t))/Π_{t+1}]`. -/
theorem bond_1631 {β ybar : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P (fun _ _ => ybar) s N0 a0 (fun _ _ => ybar) m a)
    (hp : PriceRegular S Λ P) (hmb : ∀ n, BddAt S (m n))
    (hucne : ∀ t ω, uc ybar (m t ω) ≠ 0)
    (hucinv : ∀ t, BddAt S fun ω => (uc ybar (m t ω))⁻¹) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 1 / (1 + (1 / bondPrice S Λ P t ω - 1)) =
      β * S.E t (fun ω => (uc ybar (m (t + 1) ω) / uc ybar (m t ω)) /
        (P (t + 1) ω / P t ω)) ω := by
  have h := bond_1915_ratio hβ hu hopt hp (fun _ => BddAt.const ybar) hmb hucne hucinv t
  have e : (fun ω => β * (uc ((fun _ _ => ybar : ℕ → Ω → ℝ) (t + 1) ω) (m (t + 1) ω) /
      uc ((fun _ _ => ybar : ℕ → Ω → ℝ) t ω) (m t ω)) * (P t ω / P (t + 1) ω)) =
      β • fun ω => (uc ybar (m (t + 1) ω) / uc ybar (m t ω)) / (P (t + 1) ω / P t ω) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, div_div_eq_mul_div]
    ring
  rw [e] at h
  filter_upwards [h, S.E_smul β _ t] with ω h1 h2
  rw [show (1 : ℝ) + (1 / bondPrice S Λ P t ω - 1) = 1 / bondPrice S Λ P t ω by ring,
    one_div_one_div, h1, h2]
  rfl

/-- Cochrane (2023), §16.10.6, p. 393: a money-demand function `L` for the endowment `y`:
`M/P = L(i)` is the unique solution of the money-versus-consumption first-order condition
`u_m(y, m)/u_c(y, m) = i/(1 + i)`. -/
def MoneyDemand (uc um : ℝ → ℝ → ℝ) (ybar : ℝ) (L : ℝ → ℝ) : Prop :=
  ∀ i mm : ℝ, um ybar mm / uc ybar mm = i / (1 + i) ↔ mm = L i

/-- Cochrane (2023), §16.10.6, p. 393, "expressing the money `u_m` vs. consumption `u_c`
first-order condition as `M_t/P_t = L(y, i_t)`", derived from optimality: almost surely
`m_t = L(i_t)` with `1 + i_t = 1/Q_t`. -/
theorem money_demand_1631 {β ybar : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um) {Λ P s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P (fun _ _ => ybar) s N0 a0 (fun _ _ => ybar) m a)
    (hp : PriceRegular S Λ P) (hmb : ∀ n, BddAt S (m n)) (hucne : ∀ t ω, uc ybar (m t ω) ≠ 0)
    {L : ℝ → ℝ} (hL : MoneyDemand uc um ybar L) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, m t ω = L (1 / bondPrice S Λ P t ω - 1) := by
  filter_upwards [money_demand_1916 hβ hu hopt hp (fun _ => BddAt.const ybar) hmb hucne t]
    with ω h
  exact (hL _ _).mp h.1

/-! ## Perfect foresight: the one-state tree -/

open ExpectationsFiniteTree TreeBridge TidyR6Household16_25.Tree

/-- Cochrane (2023), §16.10.6, p. 393 ("This is a perfect-foresight model"): on the one-state
tree the measure-theoretic `E_t` is the identity. -/
theorem unit_E (t : ℕ) (x : Unit → ℝ) : (treeSystem unitTree).E t x = x := by
  rw [treeSystem_E, ← FiniteTree.toExpectationSystem_E, unitTree_E]

/-- Cochrane (2023), §16.10.6, p. 393: on the one-state tree the bond price is
`Q_t = (Λ_{t+1}/P_{t+1})/(Λ_t/P_t)`. -/
theorem unit_bondPrice (Λ P : ℕ → Unit → ℝ) (t : ℕ) :
    bondPrice (treeSystem unitTree) Λ P t () =
      (Λ (t + 1) () / P (t + 1) ()) / (Λ t () / P t ()) := by
  unfold bondPrice
  rw [unit_E]
  rfl

/-- Cochrane (2023), eq. (16.31), p. 393, **perfect foresight, necessary and sufficient**: on the
one-state tree, with jointly concave smooth utility, regular prices normalised by
`Λ_0 = u_c(y, m_0)`, `u_c(y, m_t) > 0`, a feasible admissible plan `c = y` with transversality,
the plan is optimal iff at every date (16.31)
`1 + i_t = Π_{t+1}u_c(y, m_t)/(βu_c(y, m_{t+1}))` and the money first-order condition
`u_m(y, m_t)/u_c(y, m_t) = i_t/(1 + i_t)` hold, where `1 + i_t = 1/Q_t`. -/
theorem pf_optimal_iff {β ybar : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    (hsup : ∀ x y x' y', u x' y' ≤ u x y + uc x y * (x' - x) + um x y * (y' - y))
    {Λ P s : ℕ → Unit → ℝ} {N0 a0 : Unit → ℝ} {m a : ℕ → Unit → ℝ}
    (hp : PriceRegular (treeSystem unitTree) Λ P)
    (hf : Feasible (treeSystem unitTree) Λ P (fun _ _ => ybar) s N0 a0 (fun _ _ => ybar) m a)
    (hadm : UAdmissible (treeSystem unitTree) β (fun n ω => u ybar (m n ω)))
    (htvc : Tendsto (wealthPV (treeSystem unitTree) Λ P N0 m a) atTop (𝓝 0))
    (hucpos : ∀ t, 0 < uc ybar (m t ())) (hnorm : Λ 0 () = uc ybar (m 0 ())) :
    MIUOptimal (treeSystem unitTree) β u Λ P (fun _ _ => ybar) s N0 a0 (fun _ _ => ybar) m a ↔
      ∀ t, 1 + (1 / bondPrice (treeSystem unitTree) Λ P t () - 1) =
          (P (t + 1) () / P t ()) * uc ybar (m t ()) / (β * uc ybar (m (t + 1) ())) ∧
        um ybar (m t ()) / uc ybar (m t ()) =
          (1 / bondPrice (treeSystem unitTree) Λ P t () - 1) /
            (1 + (1 / bondPrice (treeSystem unitTree) Λ P t () - 1)) := by
  have hΛ : ∀ t, 0 < Λ t () := fun t => hp.2.2.1 t ()
  have hP : ∀ t, 0 < P t () := fun t => hp.2.2.2.1 t ()
  rw [optimal_iff_foc hβ hu hsup hp (fun _ => Integrable.of_finite)
    (fun _ => Integrable.of_finite) hf hadm htvc (fun _ => TreeLink.bddAt_of_finite _ _)
    (fun _ => TreeLink.bddAt_of_finite _ _) (fun ω => by cases ω; exact hnorm)]
  have hae : ∀ p : Unit → Prop, (∀ᵐ ω ∂(treeSystem unitTree).μ, p ω) ↔ p () :=
    fun p => ⟨fun h => TreeLink.forall_of_ae unitTree h (), fun h =>
      Eventually.of_forall fun ω => by cases ω; exact h⟩
  simp only [hae]
  simp only [iota, unit_bondPrice]
  have hQpos : ∀ t, 0 < Λ (t + 1) () / P (t + 1) () / (Λ t () / P t ()) := fun t =>
    div_pos (div_pos (hΛ _) (hP _)) (div_pos (hΛ _) (hP _))
  have hiota : ∀ t, (1 / (Λ (t + 1) () / P (t + 1) () / (Λ t () / P t ())) - 1) /
      (1 + (1 / (Λ (t + 1) () / P (t + 1) () / (Λ t () / P t ())) - 1)) =
      1 - Λ (t + 1) () / P (t + 1) () / (Λ t () / P t ()) := fun t => by
    have hQ := (hQpos t).ne'
    generalize Λ (t + 1) () / P (t + 1) () / (Λ t () / P t ()) = Q at hQ ⊢
    rw [show 1 + (1 / Q - 1) = 1 / Q by ring]
    field_simp
  simp only [hiota]
  constructor
  · intro h t
    obtain ⟨h1, h2⟩ := h t
    obtain ⟨h3, -⟩ := h (t + 1)
    have hc := hucpos t
    have hc' := hucpos (t + 1)
    refine ⟨?_, ?_⟩
    · rw [← h1, ← h3]
      have := hP t
      have := hP (t + 1)
      field_simp
      ring
    · rw [div_eq_iff hc.ne']
      have hb : 0 < β ^ t := pow_pos hβ t
      apply mul_left_cancel₀ hb.ne'
      rw [h2, ← h1]
      ring
  · intro h
    have hΛeq : ∀ t, β ^ t * uc ybar (m t ()) = Λ t () := by
      intro t
      induction t with
      | zero => simp [hnorm]
      | succ n ih =>
        obtain ⟨h1, -⟩ := h n
        have hc := hucpos n
        have hc' := hucpos (n + 1)
        have hPn := hP n
        have hPn' := hP (n + 1)
        have hΛn' := hΛ (n + 1)
        have hbn := pow_pos hβ n
        rw [← ih] at h1
        field_simp at h1
        rw [pow_succ]
        have h2 : (P (n + 1) () * uc ybar (m n ())) * (β ^ n * β * uc ybar (m (n + 1) ())) =
            (P (n + 1) () * uc ybar (m n ())) * Λ (n + 1) () := by linear_combination h1
        exact mul_left_cancel₀ (mul_pos hPn' hc).ne' h2
    intro t
    refine ⟨hΛeq t, ?_⟩
    obtain ⟨-, h2⟩ := h t
    have hc := hucpos t
    rw [div_eq_iff hc.ne'] at h2
    rw [h2, ← hΛeq t]
    ring

/-- Cochrane (2023), eqs. (16.31)–(16.32), p. 393, derived from optimisation under perfect
foresight: if the plan is optimal on the one-state tree (hypotheses of `pf_optimal_iff`), the
central bank follows `1 + i_t = Φ(Π_t)/β` and money demand is `m_t = L(i_t)` at dates `t + 1`
and `t + 2`, then `Π_{t+2} = Φ(Π_{t+1})k(Π_{t+2})/k(Π_{t+1})` with
`k(Π) = u_c(y, L(Φ(Π)/β − 1))`: (16.32). -/
theorem pf_1632_of_optimal {β ybar : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um)
    (hsup : ∀ x y x' y', u x' y' ≤ u x y + uc x y * (x' - x) + um x y * (y' - y))
    {Λ P s : ℕ → Unit → ℝ} {N0 a0 : Unit → ℝ} {m a : ℕ → Unit → ℝ}
    (hp : PriceRegular (treeSystem unitTree) Λ P)
    (hf : Feasible (treeSystem unitTree) Λ P (fun _ _ => ybar) s N0 a0 (fun _ _ => ybar) m a)
    (hadm : UAdmissible (treeSystem unitTree) β (fun n ω => u ybar (m n ω)))
    (htvc : Tendsto (wealthPV (treeSystem unitTree) Λ P N0 m a) atTop (𝓝 0))
    (hucpos : ∀ t, 0 < uc ybar (m t ())) (hnorm : Λ 0 () = uc ybar (m 0 ()))
    (hopt : MIUOptimal (treeSystem unitTree) β u Λ P (fun _ _ => ybar) s N0 a0
      (fun _ _ => ybar) m a)
    {Φ L : ℝ → ℝ} (t : ℕ)
    (hrule : ∀ n, 1 + (1 / bondPrice (treeSystem unitTree) Λ P (n + 1) () - 1) =
      Φ (P (n + 1) () / P n ()) / β)
    (hL : ∀ n, m (n + 1) () = L (1 / bondPrice (treeSystem unitTree) Λ P (n + 1) () - 1)) :
    P (t + 2) () / P (t + 1) () =
      Φ (P (t + 1) () / P t ()) * uc ybar (L (Φ (P (t + 2) () / P (t + 1) ()) / β - 1)) /
        uc ybar (L (Φ (P (t + 1) () / P t ()) / β - 1)) := by
  have h := ((pf_optimal_iff hβ hu hsup hp hf hadm htvc hucpos hnorm).mp hopt (t + 1)).1
  have hk : ∀ n, uc ybar (m (n + 1) ()) = uc ybar (L (Φ (P (n + 1) () / P n ()) / β - 1)) := by
    intro n
    rw [hL n]
    congr 2
    linarith [hrule n]
  rw [hrule t, hk t, hk (t + 1)] at h
  have hk0 := hk t ▸ hucpos (t + 1)
  have hk1 := hk (t + 1) ▸ hucpos (t + 2)
  exact (SelectionPatches.eq1632_iff (k := fun x => uc ybar (L (Φ x / β - 1))) hβ hk0 hk1).mp h

end Cochrane.NewKeynesianSelection.TidyR6Household16_31
