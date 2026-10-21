/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.PolicyRulesMeasureNews

/-!
# Strict stationarity at `ρ = 1` in a probability model

Cochrane (2023), §5.4.1, pp. 136–137 and §5.5, p. 148 ("ρ ≤ 1 … this equation has a
forward-looking or unit root. Therefore the unique stationary equilibrium has `v = v*`"), with
the differenced fiscal equation (5.63) (corrected date, E39). At `ρ = 1` the gap `d = v* − v`
obeys `d_{t+1} = d_t + (π_{t+1} − π*_{t+1})`, a martingale (by (5.57)). The core
`ExpectationSystem` has no laws, hence no stationarity; a `MeasExpectationSystem` does, so the
book's "stationary" can now be stated as **strict stationarity**: the law of the shifted path
`(d_{t+k})_k` equals the law of `(d_k)_k` (`StrictlyStationary`).

Results (survey E32, made precise):

* `stationary_martingale`: a bounded strictly stationary martingale has zero increments a.e.
  (second moments: `E d_{t+1}² = E d_t² + E ν_{t+1}²`).
* `rho_one_stationary_iff`: at `ρ = 1`, for every bounded adapted solution of the full model,
  `d = v* − v` is strictly stationary **iff** `π*_{t+1} = π_{t+1}` a.e. at every date; then
  `d_t = d_0` a.e. (`rho_one_stationary_const`). So strict stationarity selects `π* = π`, which
  boundedness alone does not.
* `rho_one_stationary_not_select`: strict stationarity does **not** select `v* = v`: a constant
  gap `d ≡ 1` is a strictly stationary bounded solution in every probability model.
* `iid_stationary_from_one`: the survey's example is stationary only from date 1: in the i.i.d.
  economy there is a bounded solution of the full model at `ρ = 1` whose gap `d` is strictly
  stationary from date 1, with `π*_1 ≠ π_1` with positive probability; by
  `rho_one_stationary_iff` it is not strictly stationary from date 0. (The survey's E32 claims a
  "bounded, strictly stationary `d ≠ 0` with `Δπ ≠ Δπ*`"; with stationarity from date 0 this is
  impossible, from date 1 it is true.)
-/

namespace Cochrane.StickyPriceFiscal.PolicyRulesMeasureStationary

open MeasureTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID PolicyRules PolicyRulesMeasure
  PolicyRulesMeasureNews

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Strict stationarity -/

/-- Cochrane (2023), §5.5, p. 148 ("the unique stationary equilibrium"), made precise: a process
is strictly stationary if every shifted path `(X_{t+k})_k` has the law of `(X_k)_k`. -/
def StrictlyStationary (X : ℕ → Ω → ℝ) : Prop :=
  ∀ t, S.μ.map (fun ω k => X (t + k) ω) = S.μ.map (fun ω k => X k ω)

/-- Cochrane (2023), §5.5, p. 148: strict stationarity from date `s` (of `(X_{s+k})_k`). -/
def StrictlyStationaryFrom (s : ℕ) (X : ℕ → Ω → ℝ) : Prop :=
  StrictlyStationary S (fun k => X (s + k))

/-- Cochrane (2023), §5.5, p. 148 (tool): a strictly stationary measurable process has the same
law at every date. -/
theorem map_eq_of_stationary {X : ℕ → Ω → ℝ} (hX : ∀ t, Measurable (X t))
    (h : StrictlyStationary S X) (t : ℕ) : S.μ.map (X t) = S.μ.map (X 0) := by
  have hm : ∀ s, Measurable (fun ω k => X (s + k) ω) := fun s =>
    Measurable.of_eval fun k => hX (s + k)
  have e := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (h t)
  rw [Measure.map_map (measurable_pi_apply 0) (hm t),
    Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval fun k => hX k)] at e
  exact e

/-- Cochrane (2023), §5.5, p. 148 (tool): a strictly stationary measurable process has the same
second moment at every date. -/
theorem integral_sq_of_stationary {X : ℕ → Ω → ℝ} (hX : ∀ t, Measurable (X t))
    (h : StrictlyStationary S X) (t : ℕ) :
    ∫ ω, X t ω ^ 2 ∂S.μ = ∫ ω, X 0 ω ^ 2 ∂S.μ := by
  have hf : Measurable (fun y : ℝ => y ^ 2) := measurable_id.pow_const 2
  rw [← integral_map (hX t).aemeasurable hf.aestronglyMeasurable,
    ← integral_map (hX 0).aemeasurable hf.aestronglyMeasurable, map_eq_of_stationary S hX h t]

/-- **A bounded strictly stationary martingale is constant** (Cochrane (2023), §5.4.1, p. 137 and
§5.5, p. 148; survey E32): if `d_{t+1} = d_t + ν_{t+1}` a.e. with `d` bounded adapted, `ν` bounded
adapted news (`E_t ν_{t+1} = 0`), and `d` strictly stationary, then `ν_{t+1} = 0` a.e. at every
date. -/
theorem stationary_martingale {d ν : ℕ → Ω → ℝ} (hda : StronglyAdapted S.𝓕 d)
    (hdb : S.BddProc d) (hνa : StronglyAdapted S.𝓕 ν) (hνb : S.BddProc ν)
    (hE : ∀ t, S.E t (ν (t + 1)) =ᵐ[S.μ] 0) (hr : ∀ t, d (t + 1) =ᵐ[S.μ] d t + ν (t + 1))
    (hst : StrictlyStationary S d) : ∀ t, ν (t + 1) =ᵐ[S.μ] 0 := by
  intro t
  obtain ⟨M, hM⟩ := hdb
  obtain ⟨B, hB⟩ := hνb
  have hνB := MeasExpectationSystem.BddRV.of_stronglyMeasurable (hνa (t + 1)) (hB (t + 1))
  have hmeas : ∀ s, Measurable (d s) := fun s => ((hda s).mono (S.𝓕.le s)).measurable
  have e1 : ∫ ω, d (t + 1) ω ^ 2 ∂S.μ = ∫ ω, (1 * d t ω + ν (t + 1) ω) ^ 2 ∂S.μ := by
    refine integral_congr_ae ?_
    filter_upwards [hr t] with ω h
    rw [h, one_mul]
    rfl
  rw [integral_sq_step S 1 (hda t) (hM t) hνB (hE t), integral_sq_of_stationary S hmeas hst,
    integral_sq_of_stationary S hmeas hst t] at e1
  have h0 : ∫ ω, ν (t + 1) ω ^ 2 ∂S.μ = 0 := by linarith
  have hsq : (fun ω => ν (t + 1) ω ^ 2) =ᵐ[S.μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
      hνB.sq.integrable).mp h0
  filter_upwards [hsq] with ω h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

/-! ### The full model at `ρ = 1` -/

/-- Cochrane (2023), eqs. (5.51)–(5.62), p. 147, in a probability model (a.e.): the full model
with the latent value `v*` and inflation target `π*`, as `PolicyRules.FullSys`. -/
def MFullSys (P : Params) (ei es ui us x p q v vs ps : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - S.E t (p (t + 1)))) ∧
  (∀ t, p t =ᵐ[S.μ] P.beta • S.E t (p (t + 1)) + P.kappa • x t) ∧
  (∀ t, P.rho • vs (t + 1) =ᵐ[S.μ] vs t + rnNext P q t - ps (t + 1) - sNext P x p vs us t) ∧
  (∀ t, P.rho • v (t + 1) =ᵐ[S.μ] v t + rnNext P q t - p (t + 1) - sNext P x p vs us t) ∧
  (∀ t, S.E t (ps (t + 1)) =ᵐ[S.μ] S.E t (p (t + 1))) ∧
  (∀ t, S.innov t (ps (t + 1)) =ᵐ[S.μ] -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)) ∧
  (∀ t, S.E t (rnNext P q t) =ᵐ[S.μ] iRule P x p ui t)

/-- Cochrane (2023), (5.63), p. 148 (corrected, E39) at `ρ = 1`, in a probability model: the gap
`d = v* − v` obeys `d_{t+1} = d_t + (π_{t+1} − π*_{t+1})` a.e., and the increment is news,
`E_t(π_{t+1} − π*_{t+1}) = 0` a.e. -/
theorem rho_one_gap {P : Params} (hρ : P.rho = 1) {ei es ui us x p q v vs ps : ℕ → Ω → ℝ}
    (hs : MFullSys S P ei es ui us x p q v vs ps) (hpa : StronglyAdapted S.𝓕 p)
    (hpb : S.BddProc p) (hpsa : StronglyAdapted S.𝓕 ps) (hpsb : S.BddProc ps) :
    (∀ t, (vs - v) (t + 1) =ᵐ[S.μ] (vs - v) t + (p - ps) (t + 1)) ∧
      ∀ t, S.E t ((p - ps) (t + 1)) =ᵐ[S.μ] 0 := by
  obtain ⟨-, -, h55, h56, h57, -, -⟩ := hs
  refine ⟨fun t => ?_, fun t => ?_⟩
  · filter_upwards [h55 t, h56 t] with ω e1 e2
    simp only [hρ, one_smul, Pi.sub_apply, Pi.add_apply] at e1 e2 ⊢
    rw [e1, e2]
    ring
  · filter_upwards [S.E_sub (int_of S hpa hpb (t + 1)) (int_of S hpsa hpsb (t + 1)) t, h57 t]
      with ω e1 e2
    change S.E t (p (t + 1) - ps (t + 1)) ω = 0
    rw [e1, Pi.sub_apply, e2, sub_self]

/-- **Strict stationarity at `ρ = 1`** (Cochrane (2023), §5.4.1, pp. 136–137 and §5.5, p. 148;
survey E32 made precise): for every bounded adapted solution of the full model at `ρ = 1`, the
gap `d = v* − v` is strictly stationary iff `π*_{t+1} = π_{t+1}` a.e. at every date. -/
theorem rho_one_stationary_iff {P : Params} (hρ : P.rho = 1)
    {ei es ui us x p q v vs ps : ℕ → Ω → ℝ} (hs : MFullSys S P ei es ui us x p q v vs ps)
    (hva : StronglyAdapted S.𝓕 v) (hvsa : StronglyAdapted S.𝓕 vs)
    (hpa : StronglyAdapted S.𝓕 p) (hpsa : StronglyAdapted S.𝓕 ps) (hvb : S.BddProc v)
    (hvsb : S.BddProc vs) (hpb : S.BddProc p) (hpsb : S.BddProc ps) :
    StrictlyStationary S (vs - v) ↔ ∀ t, ps (t + 1) =ᵐ[S.μ] p (t + 1) := by
  obtain ⟨hr, hE⟩ := rho_one_gap S hρ hs hpa hpb hpsa hpsb
  constructor
  · intro hst t
    have h := stationary_martingale S (fun s => (hvsa s).sub (hva s)) (mbdd_sub S hvsb hvb)
      (fun s => (hpa s).sub (hpsa s)) (mbdd_sub S hpb hpsb) hE hr hst t
    filter_upwards [h] with ω e
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at e
    exact e.symm
  · intro h
    have hc : ∀ t, (vs - v) t =ᵐ[S.μ] (vs - v) 0 := by
      intro t
      induction t with
      | zero => exact EventuallyEq.rfl
      | succ t ih =>
        filter_upwards [hr t, ih, h t] with ω e1 e2 e3
        rw [e1, Pi.add_apply, e2]
        simp [e3]
    have hall : (fun ω k => (vs - v) k ω) =ᵐ[S.μ] fun ω _ => (vs - v) 0 ω := by
      filter_upwards [ae_all_iff.2 hc] with ω e
      funext k
      exact e k
    intro t
    have hall' : (fun ω k => (vs - v) (t + k) ω) =ᵐ[S.μ] fun ω _ => (vs - v) 0 ω := by
      filter_upwards [ae_all_iff.2 hc] with ω e
      funext k
      exact e (t + k)
    rw [Measure.map_congr hall', Measure.map_congr hall]

/-- Cochrane (2023), §5.5, p. 148 (what stationarity selects at `ρ = 1`): if the gap
`d = v* − v` of a bounded adapted solution is strictly stationary, it is constant a.e.,
`d_t = d_0`. -/
theorem rho_one_stationary_const {P : Params} (hρ : P.rho = 1)
    {ei es ui us x p q v vs ps : ℕ → Ω → ℝ} (hs : MFullSys S P ei es ui us x p q v vs ps)
    (hva : StronglyAdapted S.𝓕 v) (hvsa : StronglyAdapted S.𝓕 vs)
    (hpa : StronglyAdapted S.𝓕 p) (hpsa : StronglyAdapted S.𝓕 ps) (hvb : S.BddProc v)
    (hvsb : S.BddProc vs) (hpb : S.BddProc p) (hpsb : S.BddProc ps)
    (hst : StrictlyStationary S (vs - v)) : ∀ t, (vs - v) t =ᵐ[S.μ] (vs - v) 0 := by
  have h := (rho_one_stationary_iff S hρ hs hva hvsa hpa hpsa hvb hvsb hpb hpsb).mp hst
  obtain ⟨hr, -⟩ := rho_one_gap S hρ hs hpa hpb hpsa hpsb
  intro t
  induction t with
  | zero => exact EventuallyEq.rfl
  | succ t ih =>
    filter_upwards [hr t, ih, h t] with ω e1 e2 e3
    rw [e1, Pi.add_apply, e2]
    simp [e3]

/-- Cochrane (2023), p. 147 (tool): the parameters with `ρ = 1` and all others zero. -/
def rhoOne : Params := { zeroParams with rho := 1 }

/-- **Stationarity does not select `v* = v`** (Cochrane (2023), §5.4.1, pp. 136–137 and §5.5,
p. 148; survey E32): in every probability model, at `ρ = 1` (all other parameters zero) the
constant gap `v* − v ≡ 1` with everything else zero is a bounded adapted solution of the full
model whose gap is strictly stationary, yet `v* ≠ v` almost surely. -/
theorem rho_one_stationary_not_select :
    MFullSys S rhoOne 0 0 0 0 0 0 0 0 (fun _ _ => 1) 0 ∧
      StrictlyStationary S ((fun _ _ => (1 : ℝ)) - 0) ∧
      ¬ (fun _ : Ω => (1 : ℝ)) =ᵐ[S.μ] 0 := by
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_⟩, fun t => rfl, fun h => ?_⟩
  · exact Eventually.of_forall fun ω => by simp [iRule, S.E_zero]
  · exact Eventually.of_forall fun ω => by simp [S.E_zero, rhoOne, zeroParams]
  · exact Eventually.of_forall fun ω => by simp [rnNext, sNext, rhoOne, zeroParams]
  · exact Eventually.of_forall fun ω => by simp [rnNext, sNext, rhoOne, zeroParams]
  · exact Eventually.of_forall fun ω => by simp [S.E_zero]
  · exact Eventually.of_forall fun ω => by simp [MeasExpectationSystem.innov, S.E_zero]
  · exact Eventually.of_forall fun ω => by simp [rnNext, iRule, S.E_zero, rhoOne, zeroParams]
  · obtain ⟨ω, hω⟩ := h.exists
    simp at hω

/-! ### The survey's example in the i.i.d. economy: stationary from date 1 only -/

/-- Cochrane (2023), §5.4.1, p. 137 (an example at `ρ = 1`): `β = 1`, `θ_sπ = −1`, `α = 1`,
`ρ = 1`, all other parameters zero. -/
def exParams : Params := { zeroParams with beta := 1, thSpi := -1, alpha := 1, rho := 1 }

/-- Cochrane (2023), §5.4.1, p. 137 (example): inflation `π_0 = 0`, `π_t = ε_1` for `t ≥ 1`. -/
def exP : ℕ → (ℕ → ℝ) → ℝ
  | 0 => 0
  | _ + 1 => shock 1

/-- Cochrane (2023), §5.4.1, p. 137 (example): `π*_0 = π*_1 = 0`, `π*_t = ε_1` for `t ≥ 2`. -/
def exPs : ℕ → (ℕ → ℝ) → ℝ
  | 0 => 0
  | 1 => 0
  | _ + 2 => shock 1

/-- Cochrane (2023), §5.4.1, p. 137 (example): `v*_1 = ε_1`, `v*_t = 0` otherwise. -/
def exVs : ℕ → (ℕ → ℝ) → ℝ
  | 0 => 0
  | 1 => shock 1
  | _ + 2 => 0

/-- Cochrane (2023), §5.4.1, p. 137 (example): `v_0 = v_1 = 0`, `v_t = −ε_1` for `t ≥ 2`. -/
def exV : ℕ → (ℕ → ℝ) → ℝ
  | 0 => 0
  | 1 => 0
  | _ + 2 => -shock 1

/-- Cochrane (2023), §5.4.1, p. 137 (example, tool): the gap `v* − v` is `0` at date 0 and `ε_1`
from date 1 on. -/
theorem ex_gap (m : ℕ) : (exVs - exV) (m + 1) = shock 1 := by
  cases m with
  | zero => funext ω; simp [exVs, exV]
  | succ m => funext ω; simp [exVs, exV]

/-- **The survey's example (E32), corrected** (Cochrane (2023), §5.4.1, pp. 136–137 and §5.5,
p. 148): in the i.i.d. economy with mean-zero bounded shocks of variance `σ² > 0`, at `ρ = 1` the
processes `exP, exPs, exV, exVs` (with zero output, bond price and disturbances) are a bounded
adapted solution of the full model; the gap `d = v* − v` is strictly stationary from date 1;
`π*_1 ≠ π_1` with positive probability; and therefore `d` is **not** strictly stationary from
date 0 (`rho_one_stationary_iff`). -/
theorem iid_stationary_from_one {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    MFullSys (iidSystem ν) exParams 0 0 0 0 0 exP 0 exV exVs exPs ∧
    StronglyAdapted (iidSystem ν).𝓕 exP ∧ StronglyAdapted (iidSystem ν).𝓕 exPs ∧
    StronglyAdapted (iidSystem ν).𝓕 exV ∧ StronglyAdapted (iidSystem ν).𝓕 exVs ∧
    (iidSystem ν).BddProc exP ∧ (iidSystem ν).BddProc exPs ∧ (iidSystem ν).BddProc exV ∧
    (iidSystem ν).BddProc exVs ∧ StrictlyStationaryFrom (iidSystem ν) 1 (exVs - exV) ∧
    ¬ exPs 1 =ᵐ[(iidSystem ν).μ] exP 1 ∧ ¬ StrictlyStationary (iidSystem ν) (exVs - exV) := by
  set S := iidSystem ν with hS
  have m1 : ∀ {t : ℕ}, 1 ≤ t → StronglyMeasurable[S.𝓕 t] (shock 1) := fun h =>
    (measurable_shock ν h).stronglyMeasurable
  have hb1 := shock_ae_bdd ν hbdd 1
  have i1 : Integrable (shock 1) S.μ :=
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable (m1 le_rfl) hb1).integrable
  have E1 : ∀ {t : ℕ}, 1 ≤ t → S.E t (shock 1) = shock 1 := fun h =>
    S.E_of_stronglyMeasurable (m1 h) i1
  have E0 : S.E 0 (shock 1) =ᵐ[S.μ] 0 := E_shock_zero hmean 0
  have hpa : StronglyAdapted S.𝓕 exP := fun t => by
    cases t with
    | zero => exact stronglyMeasurable_zero
    | succ t => exact m1 (Nat.succ_pos t)
  have hpsa : StronglyAdapted S.𝓕 exPs := fun t => by
    rcases t with _ | _ | t
    · exact stronglyMeasurable_zero
    · exact stronglyMeasurable_zero
    · exact m1 (by omega)
  have hva : StronglyAdapted S.𝓕 exV := fun t => by
    rcases t with _ | _ | t
    · exact stronglyMeasurable_zero
    · exact stronglyMeasurable_zero
    · exact (m1 (by omega)).neg
  have hvsa : StronglyAdapted S.𝓕 exVs := fun t => by
    rcases t with _ | _ | t
    · exact stronglyMeasurable_zero
    · exact m1 le_rfl
    · exact stronglyMeasurable_zero
  have hB : ∀ᵐ ω ∂S.μ, |shock 1 ω| ≤ |B| := hb1.mono fun ω h => h.trans (le_abs_self B)
  have z : ∀ᵐ ω ∂S.μ, |(0 : (ℕ → ℝ) → ℝ) ω| ≤ |B| := Eventually.of_forall fun ω => by simp
  have hpb : S.BddProc exP := ⟨|B|, fun t => by
    cases t with
    | zero => exact z
    | succ t => exact hB⟩
  have hpsb : S.BddProc exPs := ⟨|B|, fun t => by
    rcases t with _ | _ | t
    · exact z
    · exact z
    · exact hB⟩
  have hvb : S.BddProc exV := ⟨|B|, fun t => by
    rcases t with _ | _ | t
    · exact z
    · exact z
    · simpa [exV] using hB⟩
  have hvsb : S.BddProc exVs := ⟨|B|, fun t => by
    rcases t with _ | _ | t
    · exact z
    · exact hB
    · exact z⟩
  have hs : MFullSys S exParams 0 0 0 0 0 exP 0 exV exVs exPs := by
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
      fun t => ?_⟩
    · exact Eventually.of_forall fun ω => by simp [iRule, S.E_zero, exParams, zeroParams]
    · cases t with
      | zero =>
        filter_upwards [E0] with ω e
        simp only [exP, exParams, zeroParams, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at e ⊢
        rw [e]
        ring
      | succ t =>
        refine Eventually.of_forall fun ω => ?_
        simp only [exP, exParams, zeroParams, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply, E1 (Nat.succ_pos t)]
        ring
    · rcases t with _ | _ | t <;> exact Eventually.of_forall fun ω => by
        simp [exVs, exPs, exP, rnNext, sNext, exParams, zeroParams]
    · rcases t with _ | _ | t <;> exact Eventually.of_forall fun ω => by
        simp [exVs, exV, exP, rnNext, sNext, exParams, zeroParams]
    · cases t with
      | zero =>
        filter_upwards [E0] with ω e
        simp only [exPs, exP, S.E_zero, Pi.zero_apply]
        exact e.symm
      | succ t => exact EventuallyEq.rfl
    · cases t with
      | zero =>
        exact Eventually.of_forall fun ω => by
          simp [exPs, MeasExpectationSystem.innov, S.E_zero, exParams, zeroParams]
      | succ t =>
        exact Eventually.of_forall fun ω => by
          simp [exPs, MeasExpectationSystem.innov, E1 (Nat.succ_pos t), E1 (Nat.succ_pos (t + 1)),
            exParams, zeroParams]
    · exact Eventually.of_forall fun ω => by
        simp [rnNext, iRule, S.E_zero, exParams, zeroParams]
  have hne : ¬ exPs 1 =ᵐ[S.μ] exP 1 := by
    intro h
    change (0 : (ℕ → ℝ) → ℝ) =ᵐ[S.μ] shock 1 at h
    exact shock_not_ae_E hmean hvar hσ 0 (h.symm.trans E0.symm)
  refine ⟨hs, hpa, hpsa, hva, hvsa, hpb, hpsb, hvb, hvsb, fun t => ?_, hne, fun hst => hne ?_⟩
  · have e1 : (fun ω k => (fun k => (exVs - exV) (1 + k)) (t + k) ω) = fun ω _ => shock 1 ω := by
      funext ω k
      simp only []
      rw [Nat.add_comm, ex_gap]
    have e2 : (fun ω k => (fun k => (exVs - exV) (1 + k)) k ω) = fun ω _ => shock 1 ω := by
      funext ω k
      simp only []
      rw [Nat.add_comm, ex_gap]
    rw [e1, e2]
  · exact (rho_one_stationary_iff S rfl hs hva hvsa hpa hpsa hvb hvsb hpb hpsb).mp hst 0

end Cochrane.StickyPriceFiscal.PolicyRulesMeasureStationary
