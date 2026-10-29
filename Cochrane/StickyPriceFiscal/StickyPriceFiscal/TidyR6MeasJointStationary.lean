/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.PolicyRulesMeasureStationary

/-!
# Strict stationarity of the equilibrium as a whole

Cochrane (2023), *The Fiscal Theory of the Price Level*, §5.4.1, pp. 136–137 and §5.5, p. 148
(after (5.63): `ρ ≤ 1`, a forward-looking or unit root, therefore "the unique stationary
equilibrium of the model includes" `v_t = v*_t`, `π_t = π*_t`), with the full model
(5.51)–(5.62) (`PolicyRulesMeasureStationary.MFullSys`). The claim is made for every `ρ ≤ 1`,
the unit root `ρ = 1` included.

`PolicyRulesMeasureStationary` states strict stationarity for the gap `v* − v` only. Here the
whole equilibrium — the ten processes `(ε_i, ε_s, u_i, u_s, x, π, q, v, v*, π*)` — is required to
be **jointly** strictly stationary: the law of the shifted vector path `(X_{t+k})_k` is the law of
`(X_k)_k` (`JointlyStationary`).

## Main results

* `stationary_of_joint`: every measurable function of a jointly stationary vector is strictly
  stationary.
* **`mfull_elim`** (`0 < ρ < 1`): in every bounded adapted solution of the full model `v* = v` and
  `π* = π` a.e. — boundedness alone selects; stationarity is not needed.
* **`rho_one_joint_select`** (`ρ = 1`): if the whole equilibrium is jointly strictly stationary,
  then `π*_{t+1} = π_{t+1}` a.e. at every date and the gap `v* − v` is constant.
* **`iid_joint_not_select`** (`ρ = 1`): in the i.i.d. economy with any bounded mean-zero shock
  law of positive variance, there is a bounded adapted solution of the full model whose whole
  ten-process vector is jointly strictly stationary, with nondegenerate shocks
  (`ε_{s,t}` not a.e. constant), and with `v* − v = −1` everywhere: **joint strict stationarity
  does not select `v = v*`** (the book's claim, made precise, is false at `ρ = 1`).
* Tools: `iid_shift` (the shift preserves `ν^ℕ`), `joint_of_coord` (processes that are fixed
  functions of the current shock are jointly stationary).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasJointStationary

open MeasureTheory Filter ExpectationsMeasure ExpectationsMeasureIID PolicyRules PolicyRulesMeasure
  PolicyRulesMeasureStationary

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), §5.5, p. 148 ("stationary equilibrium"), for the equilibrium as a whole: a
family of processes is jointly strictly stationary if every shifted vector path `(X_{t+k})_k` has
the law of `(X_k)_k`. -/
def JointlyStationary {ι : Type*} (X : ι → ℕ → Ω → ℝ) : Prop :=
  ∀ t, S.μ.map (fun ω k i => X i (t + k) ω) = S.μ.map (fun ω k i => X i k ω)

/-- Cochrane (2023), §5.5, p. 148 (tool): every measurable function of a jointly stationary
vector of measurable processes is strictly stationary. -/
theorem stationary_of_joint {ι : Type*} {X : ι → ℕ → Ω → ℝ} (hX : ∀ i t, Measurable (X i t))
    (h : JointlyStationary S X) {φ : (ι → ℝ) → ℝ} (hφ : Measurable φ) :
    StrictlyStationary S (fun t ω => φ (fun i => X i t ω)) := by
  intro t
  have hΦ : Measurable fun (f : ℕ → ι → ℝ) (k : ℕ) => φ (f k) :=
    Measurable.of_eval fun k => hφ.comp (measurable_pi_apply k)
  have hm : ∀ s, Measurable fun ω (k : ℕ) (i : ι) => X i (s + k) ω := fun s =>
    Measurable.of_eval fun k => Measurable.of_eval fun i => hX i (s + k)
  have e1 := congrArg (Measure.map fun (f : ℕ → ι → ℝ) (k : ℕ) => φ (f k)) (h t)
  rw [Measure.map_map hΦ (hm t)] at e1
  have hm0 : Measurable fun ω (k : ℕ) (i : ι) => X i k ω :=
    Measurable.of_eval fun k => Measurable.of_eval fun i => hX i k
  rw [Measure.map_map hΦ hm0] at e1
  exact e1

/-- Cochrane (2023), (5.51)–(5.62), p. 147: the ten processes of the full model as one vector
`(ε_i, ε_s, u_i, u_s, x, π, q, v, v*, π*)`. -/
def fullVec (ei es ui us x p q v vs ps : ℕ → Ω → ℝ) : Fin 10 → ℕ → Ω → ℝ :=
  ![ei, es, ui, us, x, p, q, v, vs, ps]

/-- Cochrane (2023), §5.5, p. 148 (the unique stationary equilibrium includes `v = v*`), for
`0 < ρ < 1`, **in a probability model**: in every bounded adapted solution of the full model the
latent value equals the value of debt and the inflation target equals inflation, a.e. at every
date. Boundedness selects; stationarity plays no role. -/
theorem mfull_elim {P : Params} (hρ0 : 0 < P.rho) (hρ1 : P.rho < 1)
    {ei es ui us x p q v vs ps : ℕ → Ω → ℝ} (hs : MFullSys S P ei es ui us x p q v vs ps)
    (hva : StronglyAdapted S.𝓕 v) (hvsa : StronglyAdapted S.𝓕 vs)
    (hpa : StronglyAdapted S.𝓕 p) (hpsa : StronglyAdapted S.𝓕 ps) (hvb : S.BddProc v)
    (hvsb : S.BddProc vs) (hpb : S.BddProc p) (hpsb : S.BddProc ps) :
    ∀ t, vs t =ᵐ[S.μ] v t ∧ ps (t + 1) =ᵐ[S.μ] p (t + 1) := by
  obtain ⟨-, -, h55, h56, h57, -, -⟩ := hs
  have hρ : |P.rho| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  set d : ℕ → Ω → ℝ := fun t => vs t - v t with hd
  have hda : StronglyAdapted S.𝓕 d := fun t => (hvsa t).sub (hva t)
  have hdb : S.BddProc d := mbdd_sub S hvsb hvb
  have hdi := int_of S hda hdb
  have hpi := int_of S hpa hpb
  have hpsi := int_of S hpsa hpsb
  -- `ρ d_{t+1} = d_t + (π − π*)_{t+1}`
  have hrec : ∀ t, ∀ᵐ ω ∂S.μ, P.rho * d (t + 1) ω = d t ω + (p (t + 1) ω - ps (t + 1) ω) := by
    intro t
    filter_upwards [h55 t, h56 t] with ω e1 e2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e1 e2
    change P.rho * (vs (t + 1) ω - v (t + 1) ω) = (vs t ω - v t ω) + (p (t + 1) ω - ps (t + 1) ω)
    linarith
  have hsol : S.Solves P.rho 0 d := by
    intro t
    have hrec' : (fun ω => d t ω + (p (t + 1) ω - ps (t + 1) ω)) =ᵐ[S.μ]
        fun ω => P.rho * d (t + 1) ω := by
      filter_upwards [hrec t] with ω e
      exact e.symm
    filter_upwards [S.E_congr hrec' t, S.E_add (hdi t) ((hpi (t + 1)).sub (hpsi (t + 1))) t,
      S.E_sub (hpi (t + 1)) (hpsi (t + 1)) t, h57 t, S.E_smul P.rho (d (t + 1)) t]
      with ω e1 e2 e3 e4 e5
    have e1' : S.E t (d t + (p (t + 1) - ps (t + 1))) ω = S.E t (P.rho • d (t + 1)) ω := e1
    rw [e2, Pi.add_apply, e3, Pi.sub_apply, e4, sub_self, add_zero, e5,
      S.E_of_stronglyMeasurable (hda t) (hdi t)] at e1'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    exact e1'
  have hz : S.Solves P.rho 0 (0 : ℕ → Ω → ℝ) := fun t => by
    filter_upwards [] with ω
    simp [S.E_zero]
  have hd0 := S.forward_unique hρ hsol hz
    (fun t => ((hda t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => aestronglyMeasurable_const) hdb (mbdd_zero S)
  intro t
  refine ⟨?_, ?_⟩
  · filter_upwards [hd0 t] with ω e
    change vs t ω - v t ω = 0 at e
    linarith
  · filter_upwards [hrec t, hd0 t, hd0 (t + 1)] with ω e1 e2 e3
    simp only [Pi.zero_apply] at e2 e3
    rw [e2, e3, mul_zero, zero_add] at e1
    linarith

/-- Cochrane (2023), §5.4.1, pp. 136–137 and §5.5, p. 148, at `ρ = 1`, **for the equilibrium as a
whole**: if the ten-process vector of a bounded adapted solution of the full model is jointly
strictly stationary (all processes measurable), then `π*_{t+1} = π_{t+1}` a.e. at every date and
the gap `v* − v` is constant a.e. -/
theorem rho_one_joint_select {P : Params} (hρ : P.rho = 1)
    {ei es ui us x p q v vs ps : ℕ → Ω → ℝ} (hs : MFullSys S P ei es ui us x p q v vs ps)
    (hva : StronglyAdapted S.𝓕 v) (hvsa : StronglyAdapted S.𝓕 vs)
    (hpa : StronglyAdapted S.𝓕 p) (hpsa : StronglyAdapted S.𝓕 ps) (hvb : S.BddProc v)
    (hvsb : S.BddProc vs) (hpb : S.BddProc p) (hpsb : S.BddProc ps)
    (hm : ∀ i t, Measurable (fullVec ei es ui us x p q v vs ps i t))
    (hjs : JointlyStationary S (fullVec ei es ui us x p q v vs ps)) :
    (∀ t, ps (t + 1) =ᵐ[S.μ] p (t + 1)) ∧ ∀ t, (vs - v) t =ᵐ[S.μ] (vs - v) 0 := by
  have hgap : StrictlyStationary S (vs - v) := by
    have := stationary_of_joint S hm hjs (φ := fun f => f 8 - f 7)
      ((measurable_pi_apply 8).sub (measurable_pi_apply 7))
    exact this
  exact ⟨(rho_one_stationary_iff S hρ hs hva hvsa hpa hpsa hvb hvsb hpb hpsb).mp hgap,
    rho_one_stationary_const S hρ hs hva hvsa hpa hpsa hvb hvsb hpb hpsb hgap⟩

/-! ### A jointly stationary equilibrium with `v ≠ v*` in the i.i.d. economy -/

variable (ν : ProbabilityMeasure ℝ)

/-- Cochrane (2023), Ch. 2, p. 29 (tool): the shift `ω ↦ (ω_{t+k})_k` preserves the i.i.d. law
`ν^ℕ`. -/
theorem iid_shift (t : ℕ) :
    (iidSystem ν).μ.map (fun ω (k : ℕ) => ω (t + k)) = (iidSystem ν).μ := by
  change (Measure.infinitePi fun _ : ℕ => (ν : Measure ℝ)).map (fun ω (k : ℕ) => ω (t + k)) =
    Measure.infinitePi fun _ : ℕ => (ν : Measure ℝ)
  refine Measure.eq_infinitePi _ fun s A hA => ?_
  have hmeas : Measurable fun (ω : ℕ → ℝ) (k : ℕ) => ω (t + k) :=
    Measurable.of_eval fun k => measurable_pi_apply (t + k)
  rw [Measure.map_apply hmeas (MeasurableSet.pi s.countable_toSet fun i _ => hA i)]
  have hpre : (fun (ω : ℕ → ℝ) (k : ℕ) => ω (t + k)) ⁻¹' Set.pi (↑s) A =
      Set.pi (↑(s.map (addLeftEmbedding t))) (fun j => A (j - t)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      addLeftEmbedding_apply, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Nat.add_sub_cancel_left]
  rw [hpre, Measure.infinitePi_pi _ fun j _ => hA (j - t), Finset.prod_map]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [addLeftEmbedding_apply, Nat.add_sub_cancel_left]

/-- Cochrane (2023), §5.5, p. 148 (tool): in the i.i.d. economy, processes that are fixed
measurable functions of the current shock, `X_i t ω = G_i(ω_t)`, are jointly strictly
stationary. -/
theorem joint_of_coord {ι : Type*} (G : ι → ℝ → ℝ) (hG : ∀ i, Measurable (G i)) :
    JointlyStationary (iidSystem ν) (fun i t (ω : ℕ → ℝ) => G i (ω t)) := by
  intro t
  have hΨ : Measurable fun (f : ℕ → ℝ) (k : ℕ) (i : ι) => G i (f k) :=
    Measurable.of_eval fun k => Measurable.of_eval fun i =>
      (hG i).comp (measurable_pi_apply k)
  have hsh : Measurable fun (ω : ℕ → ℝ) (k : ℕ) => ω (t + k) :=
    Measurable.of_eval fun k => measurable_pi_apply (t + k)
  have e : (fun (ω : ℕ → ℝ) (k : ℕ) (i : ι) => G i (ω (t + k))) =
      (fun (f : ℕ → ℝ) (k : ℕ) (i : ι) => G i (f k)) ∘ fun ω k => ω (t + k) := rfl
  rw [e, ← Measure.map_map hΨ hsh, iid_shift ν t]

/-- Cochrane (2023), §5.4.1, p. 137 (an example at `ρ = 1`): `α = 1`, `ρ = 1`, all other
parameters zero. -/
def jParams : Params := { zeroParams with alpha := 1, rho := 1 }

/-- Cochrane (2023), §5.4.1, p. 137 (example): the shock-coordinate functions of the ten
processes, `(0, y, 0, y, 0, 0, 0, 1 − y, −y, 0)`. -/
def jG : Fin 10 → ℝ → ℝ := ![0, id, 0, id, 0, 0, 0, fun y => 1 - y, fun y => -y, 0]

/-- Cochrane (2023), §5.4.1, pp. 136–137 and §5.5, p. 148, at `ρ = 1`: **joint strict
stationarity does not select `v = v*`.** In the i.i.d. economy with bounded mean-zero shocks of
positive variance, the processes `ε_{s,t} = u_{s,t} = ω_t`, `v*_t = −ω_t`, `v_t = 1 − ω_t`, all
others zero, form a bounded adapted solution of the full model at `ρ = 1` (`α = 1`) whose whole
vector is jointly strictly stationary, whose fiscal shock is genuinely random, and whose gap is
`v* − v = −1` everywhere. -/
theorem iid_joint_not_select {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    MFullSys (iidSystem ν) jParams 0 shock 0 shock 0 0 0 (fun t ω => 1 - shock t ω)
        (fun t ω => -shock t ω) 0 ∧
      StronglyAdapted (iidSystem ν).𝓕 (fun t ω => 1 - shock t ω) ∧
      StronglyAdapted (iidSystem ν).𝓕 (fun t ω => -shock t ω) ∧
      (iidSystem ν).BddProc (fun t ω => 1 - shock t ω) ∧
      (iidSystem ν).BddProc (fun t ω => -shock t ω) ∧
      JointlyStationary (iidSystem ν) (fullVec 0 shock 0 shock 0 0 0 (fun t ω => 1 - shock t ω)
        (fun t ω => -shock t ω) 0) ∧
      (∀ t ω, (fun t ω => -shock t ω) t ω - (fun t ω => 1 - shock t ω) t ω = -1) ∧
      ∀ t, ¬ shock (t + 1) =ᵐ[(iidSystem ν).μ] (iidSystem ν).E t (shock (t + 1)) := by
  set S := iidSystem ν
  have hm : ∀ t, StronglyMeasurable[S.𝓕 t] (shock t) := fun t =>
    (measurable_shock ν le_rfl).stronglyMeasurable
  have hB : ∀ t, ∀ᵐ ω ∂S.μ, |shock t ω| ≤ B := fun t => shock_ae_bdd ν hbdd t
  have hE : ∀ t, S.E t (shock (t + 1)) =ᵐ[S.μ] 0 := fun t => E_shock_zero hmean t
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_⟩, fun t => stronglyMeasurable_const.sub (hm t), fun t => (hm t).neg,
    ⟨1 + |B|, fun t => ?_⟩, ⟨|B|, fun t => ?_⟩, ?_, fun t ω => by ring,
    fun t => shock_not_ae_E hmean hvar hσ t⟩
  · exact Eventually.of_forall fun ω => by simp [iRule, S.E_zero, jParams, zeroParams]
  · exact Eventually.of_forall fun ω => by simp [S.E_zero, jParams, zeroParams]
  · exact Eventually.of_forall fun ω => by
      simp [rnNext, sNext, jParams, zeroParams]
  · exact Eventually.of_forall fun ω => by
      simp [rnNext, sNext, jParams, zeroParams]
      ring
  · exact Eventually.of_forall fun ω => by simp [S.E_zero]
  · exact Eventually.of_forall fun ω => by
      simp [MeasExpectationSystem.innov, S.E_zero, jParams, zeroParams]
  · exact Eventually.of_forall fun ω => by
      simp [rnNext, iRule, S.E_zero, jParams, zeroParams]
  · filter_upwards [hB t] with ω h
    exact (abs_sub _ _).trans (by rw [abs_one]; linarith [le_abs_self B])
  · filter_upwards [hB t] with ω h
    rw [abs_neg]
    exact h.trans (le_abs_self B)
  · have hG : ∀ i, Measurable (jG i) := by
      intro i
      fin_cases i <;> simp only [jG, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val] <;> fun_prop
    have e : fullVec 0 shock 0 shock 0 0 0 (fun t ω => 1 - shock t ω) (fun t ω => -shock t ω) 0 =
        fun i t (ω : ℕ → ℝ) => jG i (ω t) := by
      funext i t ω
      fin_cases i <;> simp [fullVec, jG, shock]
    rw [e]
    exact joint_of_coord ν jG hG

end Cochrane.StickyPriceFiscal.TidyR6MeasJointStationary
