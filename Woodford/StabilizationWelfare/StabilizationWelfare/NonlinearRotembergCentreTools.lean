/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Tools for a non-hyperbolic planar map: a cone lemma, centre monotonicity and a Ważewski lemma

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3
(pp. 632–634): on the boundary of the Taylor principle the linearised model has a unit root, and
whether the exact model is determinate is decided by the dynamics on the centre direction. This
module proves the three one-dimensional-centre facts used for the exact Rotemberg model in
`NonlinearRotembergCentre`, for an abstract planar recursion with a NEUTRAL coordinate `L` and an
EXPANDING coordinate `V` (factor `μ > 1`):
`L_{t+1} = L_t + D_t + ν`, `V_{t+1} = μ V_t + E_t + c ν`.

* **`cone_bound`** (the invariant-cone argument): if the nonlinear terms are at most
  `η(|L| + |V|)` with `η` small, every BOUNDED orbit stays in the cone
  `|V_t| ≤ Λ|L_t| + M|ν|` at every date: outside it `|V|` grows geometrically.
* **`centre_nonpos`**, **`centre_tendsto`**, **`centre_neg_of_neg`** (the centre dynamics): if
  `D_t ≥ aL_t²` with `a > 0` and `ν = 0`, a bounded orbit has `L_t ≤ 0` at every date, is
  nondecreasing and tends to `0`; `centre_drift_unbounded`: a uniform positive drift is
  impossible for a bounded orbit.
* **`wazewski`** (existence by the Ważewski / nested-interval argument): if a planar map `T` is
  continuous on the cone region `R = {−ℓ₀ ≤ L ≤ 0, |V| ≤ Λ|L|}`, does not decrease `L`, keeps
  `L < 0`, and maps each side of the cone strictly outside through the same side, then for every
  `L₀ ∈ [−ℓ₀, 0)` some `V₀` has its whole forward orbit in `R`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergCentreTools

open Filter Topology

/-! ## The invariant cone -/

/-- Woodford (2003), App. A.3 (the expanding direction): one step of the cone argument. If
`|V| > Λ|L| + M|ν|`, then `|V′| ≥ λ|V|` and `|V′| > Λ|L′| + M|ν|` with `λ = (1 + μ)/2`. -/
theorem cone_step {μ Λ M η ν c L V D E : ℝ} (hΛ : 0 < Λ) (hM : 0 < M) (hη : 0 ≤ η)
    (hD : |D| ≤ η * (|L| + |V|)) (hE : |E| ≤ η * (|L| + |V|))
    (h1 : η * (1 + 1 / Λ) + |c| / M ≤ (μ - 1) / 2) (h2 : η * (Λ + 1) + Λ / M ≤ (μ - 1) / 2)
    (hout : Λ * |L| + M * |ν| < |V|) :
    (1 + μ) / 2 * |V| ≤ |μ * V + E + c * ν| ∧
      Λ * |L + D + ν| + M * |ν| < |μ * V + E + c * ν| := by
  have hV0 : 0 < |V| := lt_of_le_of_lt (by positivity) hout
  have hLV : Λ * |L| < |V| := by nlinarith [abs_nonneg ν]
  have hL : |L| ≤ |V| / Λ := by rw [le_div_iff₀ hΛ]; linarith
  have hν : |ν| ≤ |V| / M := by rw [le_div_iff₀ hM]; nlinarith [abs_nonneg L]
  have hs : |L| + |V| ≤ (1 + 1 / Λ) * |V| := by
    have : |V| / Λ = 1 / Λ * |V| := by ring
    linarith
  have hDs : η * (|L| + |V|) ≤ η * ((1 + 1 / Λ) * |V|) := mul_le_mul_of_nonneg_left hs hη
  have hcν : |c * ν| ≤ |c| / M * |V| := by
    rw [abs_mul]
    calc |c| * |ν| ≤ |c| * (|V| / M) := mul_le_mul_of_nonneg_left hν (abs_nonneg c)
      _ = |c| / M * |V| := by ring
  have hμ0 : 0 < μ := by
    have : 0 ≤ η * (1 + 1 / Λ) + |c| / M := by positivity
    linarith
  have hμV : |μ * V| = μ * |V| := by
    rw [abs_mul, abs_of_pos hμ0]
  have hlow : (1 + μ) / 2 * |V| ≤ |μ * V + E + c * ν| := by
    have t1 : |μ * V| - |E| - |c * ν| ≤ |μ * V + E + c * ν| := by
      have a := abs_sub_abs_le_abs_sub (μ * V) (-(E + c * ν))
      rw [abs_neg, sub_neg_eq_add, ← add_assoc] at a
      have b := abs_add_le E (c * ν)
      linarith
    rw [hμV] at t1
    have : η * ((1 + 1 / Λ) * |V|) + |c| / M * |V| ≤ (μ - 1) / 2 * |V| := by
      have := mul_le_mul_of_nonneg_right h1 hV0.le
      nlinarith
    linarith
  refine ⟨hlow, ?_⟩
  have hL' : |L + D + ν| ≤ |L| + η * ((1 + 1 / Λ) * |V|) + |ν| := by
    have := abs_add_le (L + D) ν
    have := abs_add_le L D
    linarith
  have key : Λ * (η * ((1 + 1 / Λ) * |V|)) + Λ * |ν| ≤ (η * (Λ + 1) + Λ / M) * |V| := by
    have e : Λ * (η * ((1 + 1 / Λ) * |V|)) = η * (Λ + 1) * |V| := by field_simp
    have f : Λ * |ν| ≤ Λ / M * |V| := by
      calc Λ * |ν| ≤ Λ * (|V| / M) := mul_le_mul_of_nonneg_left hν hΛ.le
        _ = Λ / M * |V| := by ring
    rw [e]; nlinarith
  have k2 := mul_le_mul_of_nonneg_right h2 hV0.le
  calc Λ * |L + D + ν| + M * |ν| ≤ Λ * (|L| + η * ((1 + 1 / Λ) * |V|) + |ν|) + M * |ν| := by
        gcongr
    _ = (Λ * |L| + M * |ν|) + (Λ * (η * ((1 + 1 / Λ) * |V|)) + Λ * |ν|) := by ring
    _ < |V| + (η * (Λ + 1) + Λ / M) * |V| := by linarith
    _ ≤ (1 + μ) / 2 * |V| := by nlinarith
    _ ≤ _ := hlow

/-- Woodford (2003), App. A.3 (**the invariant-cone lemma**): along a recursion
`L_{t+1} = L_t + D_t + ν`, `V_{t+1} = μV_t + E_t + cν` with `|D_t|, |E_t| ≤ η(|L_t| + |V_t|)` and
`η` small relative to `μ − 1 > 0`, every orbit with `V` bounded stays in the cone
`|V_t| ≤ Λ|L_t| + M|ν|` at every date. -/
theorem cone_bound {μ Λ M η ν c B : ℝ} {L V D E : ℕ → ℝ} (hμ : 1 < μ) (hΛ : 0 < Λ) (hM : 0 < M)
    (hη : 0 ≤ η) (h1 : η * (1 + 1 / Λ) + |c| / M ≤ (μ - 1) / 2)
    (h2 : η * (Λ + 1) + Λ / M ≤ (μ - 1) / 2)
    (hL : ∀ t, L (t + 1) = L t + D t + ν) (hV : ∀ t, V (t + 1) = μ * V t + E t + c * ν)
    (hD : ∀ t, |D t| ≤ η * (|L t| + |V t|)) (hE : ∀ t, |E t| ≤ η * (|L t| + |V t|))
    (hB : ∀ t, |V t| ≤ B) (t : ℕ) : |V t| ≤ Λ * |L t| + M * |ν| := by
  by_contra hc
  push Not at hc
  have hgrow : ∀ n : ℕ, ((1 + μ) / 2) ^ n * |V t| ≤ |V (t + n)| ∧
      Λ * |L (t + n)| + M * |ν| < |V (t + n)| := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
      obtain ⟨s1, s2⟩ := cone_step hΛ hM hη (hD (t + n)) (hE (t + n)) h1 h2 ih.2
      rw [← add_assoc, hV, hL]
      refine ⟨?_, s2⟩
      calc ((1 + μ) / 2) ^ (n + 1) * |V t| = (1 + μ) / 2 * (((1 + μ) / 2) ^ n * |V t|) := by
            ring
        _ ≤ (1 + μ) / 2 * |V (t + n)| := by
            gcongr
            exact ih.1
        _ ≤ _ := s1
  have hV0 : 0 < |V t| := lt_of_le_of_lt (by positivity) hc
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / |V t|) (by linarith : (1 : ℝ) < (1 + μ) / 2)
  have := (hgrow n).1
  rw [div_lt_iff₀ hV0] at hn
  linarith [hB (t + n)]

/-! ## The centre dynamics -/

/-- Woodford (2003), App. A.3 (**a bounded orbit cannot drift**): if `L_{t+1} ≥ L_t + d` with
`d > 0` at every date, `L` is unbounded. -/
theorem centre_drift_unbounded {L : ℕ → ℝ} {d B : ℝ} (hd : 0 < d)
    (h : ∀ t, L t + d ≤ L (t + 1)) (hB : ∀ t, |L t| ≤ B) : False := by
  have hn : ∀ n : ℕ, L 0 + n * d ≤ L n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => push_cast; linarith [h n]
  obtain ⟨n, hn'⟩ := exists_nat_gt ((2 * B + 1) / d)
  rw [div_lt_iff₀ hd] at hn'
  have a := hn n
  have b := abs_le.1 (hB 0)
  have c := abs_le.1 (hB n)
  linarith

/-- Woodford (2003), App. A.3 (**the centre coordinate of a bounded orbit is never positive**):
if `L_{t+1} = L_t + D_t` with `D_t ≥ aL_t²`, `a > 0`, and `L` is bounded, then `L_t ≤ 0` at every
date. -/
theorem centre_nonpos {L D : ℕ → ℝ} {a B : ℝ} (ha : 0 < a) (hL : ∀ t, L (t + 1) = L t + D t)
    (hD : ∀ t, a * L t ^ 2 ≤ D t) (hB : ∀ t, |L t| ≤ B) (t : ℕ) : L t ≤ 0 := by
  by_contra hc
  push Not at hc
  have hmono : ∀ n, L t ≤ L (t + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, hL]
      nlinarith [hD (t + n), sq_nonneg (L (t + n))]
  refine centre_drift_unbounded (L := fun n => L (t + n)) (d := a * L t ^ 2) (B := B)
    (by positivity) (fun n => ?_) (fun n => hB (t + n))
  show L (t + n) + a * L t ^ 2 ≤ L (t + (n + 1))
  rw [← add_assoc, hL]
  have h1 := hmono n
  have h2 : L t ^ 2 ≤ L (t + n) ^ 2 := by nlinarith
  nlinarith [hD (t + n)]

/-- Woodford (2003), App. A.3 (**the centre coordinate of a bounded orbit converges to `0`**): if
`L_{t+1} = L_t + D_t` with `D_t ≥ aL_t²`, `a > 0`, and `L` is bounded, then `L` is nondecreasing
and `L_t → 0`. -/
theorem centre_tendsto {L D : ℕ → ℝ} {a B : ℝ} (ha : 0 < a) (hL : ∀ t, L (t + 1) = L t + D t)
    (hD : ∀ t, a * L t ^ 2 ≤ D t) (hB : ∀ t, |L t| ≤ B) :
    Monotone L ∧ Tendsto L atTop (𝓝 0) := by
  have hmono : Monotone L := monotone_nat_of_le_succ fun n => by
    rw [hL]; nlinarith [hD n, sq_nonneg (L n)]
  refine ⟨hmono, ?_⟩
  have hbdd : BddAbove (Set.range L) := ⟨0, by
    rintro _ ⟨n, rfl⟩; exact centre_nonpos ha hL hD hB n⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set ℓ := ⨆ n, L n with hℓ
  -- `aL_t² ≤ L_{t+1} − L_t → 0`
  have hdiff : Tendsto (fun n => L (n + 1) - L n) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa using this
  have hsq : Tendsto (fun n => a * L n ^ 2) atTop (𝓝 (a * ℓ ^ 2)) :=
    (hlim.pow 2).const_mul a
  have hle : a * ℓ ^ 2 ≤ 0 := by
    refine le_of_tendsto_of_tendsto hsq hdiff (Eventually.of_forall fun n => ?_)
    change a * L n ^ 2 ≤ L (n + 1) - L n
    rw [hL]; linarith [hD n]
  have hℓ0 : ℓ = 0 := by
    have : ℓ ^ 2 ≤ 0 := by
      by_contra h; push Not at h; nlinarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg ℓ))
  rw [← hℓ0]; exact hlim

/-- Woodford (2003), App. A.3 (**a negative start stays negative**): if `L_{t+1} = L_t + D_t`
with `|D_t| ≤ |L_t|/2` at every date and `L_0 < 0`, then `L_t < 0` at every date. -/
theorem centre_neg_of_neg {L D : ℕ → ℝ} (hL : ∀ t, L (t + 1) = L t + D t)
    (hD : ∀ t, |D t| ≤ |L t| / 2) (h0 : L 0 < 0) (t : ℕ) : L t < 0 := by
  induction t with
  | zero => exact h0
  | succ n ih =>
    rw [hL]
    have := (abs_le.1 (hD n)).2
    rw [abs_of_neg ih] at this
    linarith

/-! ## Existence: the Ważewski nested-interval argument -/

/-- Woodford (2003), App. A.3: The cone region `R = {−ℓ₀ ≤ L ≤ 0, |V| ≤ Λ|L|}` of the plane `(L,
V)`. -/
def coneR (ℓ0 Λ : ℝ) : Set (ℝ × ℝ) := {q | -ℓ0 ≤ q.1 ∧ q.1 ≤ 0 ∧ |q.2| ≤ Λ * |q.1|}

/-- Woodford (2003), App. A.3: The cone region is closed. -/
theorem isClosed_coneR (ℓ0 Λ : ℝ) : IsClosed (coneR ℓ0 Λ) := by
  refine (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_const).inter
      (isClosed_le (continuous_abs.comp continuous_snd)
        (continuous_const.mul (continuous_abs.comp continuous_fst))))

variable {T : ℝ × ℝ → ℝ × ℝ} {ℓ0 Λ : ℝ}

/-- Woodford (2003), App. A.3: The points of the segment `{L₀} × [−Λ|L₀|, Λ|L₀|]` whose orbit stays
in `R` up to date `n`. -/
def Kset (T : ℝ × ℝ → ℝ × ℝ) (ℓ0 Λ L0 : ℝ) (n : ℕ) : Set ℝ :=
  {s | s ∈ Set.Icc (-(Λ * |L0|)) (Λ * |L0|) ∧ ∀ j ≤ n, T^[j] (L0, s) ∈ coneR ℓ0 Λ}

/-- Woodford (2003), App. A.3: `K_{n+1} = K_n ∩ {s : T^{n+1}(L₀, s) ∈ R}`. -/
theorem Kset_succ (L0 : ℝ) (n : ℕ) :
    Kset T ℓ0 Λ L0 (n + 1) = Kset T ℓ0 Λ L0 n ∩ {s | T^[n + 1] (L0, s) ∈ coneR ℓ0 Λ} := by
  ext s
  simp only [Kset, Set.mem_inter_iff]
  constructor
  · rintro ⟨h0, h⟩
    exact ⟨⟨h0, fun j hj => h j (by omega)⟩, h (n + 1) le_rfl⟩
  · rintro ⟨⟨h0, h⟩, h'⟩
    refine ⟨h0, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
    · exact h j (by omega)
    · rwa [show j = n + 1 by omega]

/-- Woodford (2003), App. A.3: Along `K_n` every iterate up to `n` has `L < 0` and `L ≥ L₀`. -/
theorem Kset_neg (hT2 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.1 ≤ (T q).1 ∧ (T q).1 < 0)
    {L0 : ℝ} (hL0 : L0 < 0) {n : ℕ} {s : ℝ} (hs : s ∈ Kset T ℓ0 Λ L0 n) :
    ∀ j ≤ n, L0 ≤ (T^[j] (L0, s)).1 ∧ (T^[j] (L0, s)).1 < 0 := by
  intro j hj
  induction j with
  | zero => simp [hL0]
  | succ j ih =>
    obtain ⟨a, b⟩ := ih (by omega)
    have h := hT2 _ (hs.2 j (by omega)) b
    rw [Function.iterate_succ_apply']
    exact ⟨a.trans h.1, h.2⟩

/-- Woodford (2003), App. A.3: The iterates are continuous on `K_n`. -/
theorem Kset_continuousOn (hT : ContinuousOn T (coneR ℓ0 Λ)) (L0 : ℝ) (n : ℕ) :
    ∀ j ≤ n + 1, ContinuousOn (fun s => T^[j] (L0, s)) (Kset T ℓ0 Λ L0 n) := by
  intro j hj
  induction j with
  | zero => simpa using (continuous_const.prodMk continuous_id).continuousOn
  | succ j ih =>
    have h1 := ih (by omega)
    have hmaps : Set.MapsTo (fun s => T^[j] (L0, s)) (Kset T ℓ0 Λ L0 n) (coneR ℓ0 Λ) :=
      fun s hs => hs.2 j (by omega)
    have := hT.comp h1 hmaps
    refine this.congr fun s _ => ?_
    simp only [Function.comp, Function.iterate_succ_apply']

/-- Woodford (2003), App. A.3: `K_n` is closed. -/
theorem isClosed_Kset (hT : ContinuousOn T (coneR ℓ0 Λ)) (L0 : ℝ) (n : ℕ) :
    IsClosed (Kset T ℓ0 Λ L0 n) := by
  induction n with
  | zero =>
    have e : Kset T ℓ0 Λ L0 0 = Set.Icc (-(Λ * |L0|)) (Λ * |L0|) ∩
        (fun s => ((L0, s) : ℝ × ℝ)) ⁻¹' coneR ℓ0 Λ := by
      ext s
      simp only [Kset, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h0, h⟩; exact ⟨h0, by simpa using h 0 le_rfl⟩
      · rintro ⟨h0, h⟩
        refine ⟨h0, fun j hj => ?_⟩
        rw [show j = 0 by omega]; simpa using h
    rw [e]
    exact isClosed_Icc.inter ((isClosed_coneR ℓ0 Λ).preimage
      (continuous_const.prodMk continuous_id))
  | succ n ih =>
    rw [Kset_succ]
    exact (Kset_continuousOn hT L0 n (n + 1) le_rfl).preimage_isClosed_of_isClosed ih
      (isClosed_coneR ℓ0 Λ)

set_option maxHeartbeats 800000 in
-- the selection of the sub-interval has many cases
/-- Woodford (2003), App. A.3 (**the nested-interval step**): for every `n` there is an interval
`[a, b] ⊆ K_n` whose left end is mapped by `Tⁿ` onto the lower side `V = −Λ|L|` of the cone and
whose right end onto the upper side `V = Λ|L|`. -/
theorem Kset_interval (hΛ : 0 < Λ) (hT : ContinuousOn T (coneR ℓ0 Λ))
    (hT2 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.1 ≤ (T q).1 ∧ (T q).1 < 0)
    (hT3 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.2 = Λ * |q.1| → Λ * |(T q).1| < (T q).2)
    (hT4 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.2 = -(Λ * |q.1|) → (T q).2 < -(Λ * |(T q).1|))
    {L0 : ℝ} (hℓ : -ℓ0 ≤ L0) (hL0 : L0 < 0) (n : ℕ) :
    ∃ a b, a ≤ b ∧ Set.Icc a b ⊆ Kset T ℓ0 Λ L0 n ∧
      (T^[n] (L0, a)).2 = -(Λ * |(T^[n] (L0, a)).1|) ∧
      (T^[n] (L0, b)).2 = Λ * |(T^[n] (L0, b)).1| := by
  induction n with
  | zero =>
    refine ⟨-(Λ * |L0|), Λ * |L0|, by
      have : 0 ≤ Λ * |L0| := by positivity
      linarith, fun s hs => ⟨hs, fun j hj => ?_⟩, by simp, by simp⟩
    rw [show j = 0 by omega]
    exact ⟨hℓ, hL0.le, abs_le.2 ⟨hs.1, hs.2⟩⟩
  | succ n ih =>
    obtain ⟨a, b, hab, hsub, ha, hb⟩ := ih
    set f : ℝ → ℝ × ℝ := fun s => T^[n + 1] (L0, s) with hf
    have hfc : ContinuousOn f (Set.Icc a b) :=
      (Kset_continuousOn hT L0 n (n + 1) le_rfl).mono hsub
    have hstep : ∀ s, f s = T (T^[n] (L0, s)) := fun s => by
      simp only [hf, Function.iterate_succ_apply']
    -- the properties of `Tⁿ` on `[a, b]`
    have hin : ∀ s ∈ Set.Icc a b, T^[n] (L0, s) ∈ coneR ℓ0 Λ := fun s hs => (hsub hs).2 n le_rfl
    have hneg : ∀ s ∈ Set.Icc a b, L0 ≤ (T^[n] (L0, s)).1 ∧ (T^[n] (L0, s)).1 < 0 :=
      fun s hs => Kset_neg hT2 hL0 (hsub hs) n le_rfl
    have hfneg : ∀ s ∈ Set.Icc a b, L0 ≤ (f s).1 ∧ (f s).1 < 0 := fun s hs => by
      rw [hstep]
      have h := hT2 _ (hin s hs) (hneg s hs).2
      exact ⟨(hneg s hs).1.trans h.1, h.2⟩
    have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
    -- the two side functions
    set gp : ℝ → ℝ := fun s => (f s).2 - Λ * |(f s).1| with hgp
    set gm : ℝ → ℝ := fun s => (f s).2 + Λ * |(f s).1| with hgm
    have hgpc : ContinuousOn gp (Set.Icc a b) :=
      (continuous_snd.comp_continuousOn hfc).sub
        (continuousOn_const.mul (continuous_abs.comp_continuousOn
          (continuous_fst.comp_continuousOn hfc)))
    have hgmc : ContinuousOn gm (Set.Icc a b) :=
      (continuous_snd.comp_continuousOn hfc).add
        (continuousOn_const.mul (continuous_abs.comp_continuousOn
          (continuous_fst.comp_continuousOn hfc)))
    have hga : gm a < 0 := by
      have h := hT4 _ (hin a haI) (hneg a haI).2 ha
      simp only [hgm, hstep]; linarith
    have hgb : 0 < gp b := by
      have h := hT3 _ (hin b hbI) (hneg b hbI).2 hb
      simp only [hgp, hstep]; linarith
    have hgap : ∀ s ∈ Set.Icc a b, gp s < gm s := fun s hs => by
      have := (hfneg s hs).2
      have : 0 < Λ * |(f s).1| := mul_pos hΛ (abs_pos.2 this.ne)
      simp only [hgp, hgm]; linarith
    -- the first point `b'` where `gp ≥ 0`
    set A := Set.Icc a b ∩ gp ⁻¹' Set.Ici 0 with hA
    have hAc : IsClosed A := hgpc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAne : A.Nonempty := ⟨b, hbI, hgb.le⟩
    have hAbdd : BddBelow A := ⟨a, fun s hs => hs.1.1⟩
    set b' := sInf A with hb'
    have hb'A : b' ∈ A := hAc.csInf_mem hAne hAbdd
    have hb'I : b' ∈ Set.Icc a b := hb'A.1
    have hbelow : ∀ s ∈ Set.Icc a b, s < b' → gp s < 0 := fun s hs hsb => by
      by_contra h; push Not at h
      exact absurd (csInf_le hAbdd ⟨hs, h⟩) (not_le.2 hsb)
    have hab' : a < b' := by
      rcases eq_or_lt_of_le hb'I.1 with h | h
      · exfalso
        have h1 : 0 ≤ gp b' := hb'A.2
        rw [← h] at h1
        linarith [hgap a haI]
      · exact h
    have hgpb' : gp b' = 0 := by
      refine le_antisymm ?_ hb'A.2
      -- `gp b'` is a limit of negative values from the left
      have hcw : ContinuousWithinAt gp (Set.Ico a b') b' :=
        (hgpc b' hb'I).mono fun s hs => ⟨hs.1, hs.2.le.trans hb'I.2⟩
      have hne : (𝓝[Set.Ico a b'] b').NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hab'.ne]
        exact ⟨hab'.le, le_rfl⟩
      exact le_of_tendsto hcw (eventually_nhdsWithin_of_forall fun s hs =>
        (hbelow s ⟨hs.1, hs.2.le.trans hb'I.2⟩ hs.2).le)
    have hgmb' : 0 < gm b' := by have := hgap b' hb'I; linarith
    -- the last point `a'` in `[a, b']` where `gm ≤ 0`
    have hIsub : Set.Icc a b' ⊆ Set.Icc a b := fun s hs => ⟨hs.1, hs.2.trans hb'I.2⟩
    set B := Set.Icc a b' ∩ gm ⁻¹' Set.Iic 0 with hB
    have hBc : IsClosed B :=
      (hgmc.mono hIsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hBne : B.Nonempty := ⟨a, ⟨le_rfl, hab'.le⟩, hga.le⟩
    have hBbdd : BddAbove B := ⟨b', fun s hs => hs.1.2⟩
    set a' := sSup B with ha'
    have ha'B : a' ∈ B := hBc.csSup_mem hBne hBbdd
    have ha'I : a' ∈ Set.Icc a b' := ha'B.1
    have habove : ∀ s ∈ Set.Icc a b', a' < s → 0 < gm s := fun s hs hsa => by
      by_contra h; push Not at h
      exact absurd (le_csSup hBbdd ⟨hs, h⟩) (not_le.2 hsa)
    have ha'b' : a' < b' := by
      rcases eq_or_lt_of_le ha'I.2 with h | h
      · exfalso
        have h1 : gm a' ≤ 0 := ha'B.2
        rw [h] at h1; linarith
      · exact h
    have hgma' : gm a' = 0 := by
      refine le_antisymm ha'B.2 ?_
      have hcw : ContinuousWithinAt gm (Set.Ioc a' b') a' :=
        ((hgmc.mono hIsub) a' ha'I).mono fun s hs => ⟨ha'I.1.trans hs.1.le, hs.2⟩
      have hne : (𝓝[Set.Ioc a' b'] a').NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc ha'b'.ne]
        exact ⟨le_rfl, ha'b'.le⟩
      exact ge_of_tendsto hcw (eventually_nhdsWithin_of_forall fun s hs =>
        (habove s ⟨ha'I.1.trans hs.1.le, hs.2⟩ hs.1).le)
    refine ⟨a', b', ha'b'.le, fun s hs => ?_, ?_, ?_⟩
    · have hsI : s ∈ Set.Icc a b := ⟨ha'I.1.trans hs.1, hs.2.trans hb'I.2⟩
      rw [Kset_succ]
      refine ⟨hsub hsI, ?_⟩
      change f s ∈ coneR ℓ0 Λ
      have hgp_le : gp s ≤ 0 := by
        rcases eq_or_lt_of_le hs.2 with h | h
        · rw [h, hgpb']
        · exact (hbelow s hsI h).le
      have hgm_ge : 0 ≤ gm s := by
        rcases eq_or_lt_of_le hs.1 with h | h
        · rw [← h, hgma']
        · exact (habove s ⟨ha'I.1.trans hs.1, hs.2⟩ h).le
      obtain ⟨h1, h2⟩ := hfneg s hsI
      refine ⟨by linarith, h2.le, abs_le.2 ⟨?_, ?_⟩⟩
      · simp only [hgm] at hgm_ge; linarith
      · simp only [hgp] at hgp_le; linarith
    · change (f a').2 = -(Λ * |(f a').1|)
      simp only [hgm] at hgma'; linarith
    · change (f b').2 = Λ * |(f b').1|
      simp only [hgp] at hgpb'; linarith

/-- Woodford (2003), App. A.3 (**the Ważewski lemma for the cone**): let `T` be continuous on the
cone region `R = {−ℓ₀ ≤ L ≤ 0, |V| ≤ Λ|L|}` (`Λ > 0`), with, at every `q ∈ R` with `L < 0`:
`L ≤ L(Tq) < 0`; `V = Λ|L| ⇒ V(Tq) > Λ|L(Tq)|`; `V = −Λ|L| ⇒ V(Tq) < −Λ|L(Tq)|` (each side is
left strictly, through itself). Then for every `L₀ ∈ [−ℓ₀, 0)` there is `V₀ ∈ [−Λ|L₀|, Λ|L₀|]`
whose whole forward orbit `Tⁿ(L₀, V₀)` stays in `R`. -/
theorem wazewski (hΛ : 0 < Λ) (hT : ContinuousOn T (coneR ℓ0 Λ))
    (hT2 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.1 ≤ (T q).1 ∧ (T q).1 < 0)
    (hT3 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.2 = Λ * |q.1| → Λ * |(T q).1| < (T q).2)
    (hT4 : ∀ q ∈ coneR ℓ0 Λ, q.1 < 0 → q.2 = -(Λ * |q.1|) → (T q).2 < -(Λ * |(T q).1|))
    {L0 : ℝ} (hℓ : -ℓ0 ≤ L0) (hL0 : L0 < 0) :
    ∃ V0, |V0| ≤ Λ * |L0| ∧ ∀ n, T^[n] (L0, V0) ∈ coneR ℓ0 Λ := by
  have hne : ∀ n, (Kset T ℓ0 Λ L0 n).Nonempty := fun n => by
    obtain ⟨a, b, hab, hsub, -, -⟩ := Kset_interval hΛ hT hT2 hT3 hT4 hℓ hL0 n
    exact ⟨a, hsub ⟨le_rfl, hab⟩⟩
  have hdec : ∀ n, Kset T ℓ0 Λ L0 (n + 1) ⊆ Kset T ℓ0 Λ L0 n := fun n => by
    rw [Kset_succ]; exact Set.inter_subset_left
  have hcpt : IsCompact (Kset T ℓ0 Λ L0 0) :=
    isCompact_Icc.of_isClosed_subset (isClosed_Kset hT L0 0) fun s hs => hs.1
  obtain ⟨s, hs⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hdec hne
    hcpt (isClosed_Kset hT L0)
  rw [Set.mem_iInter] at hs
  exact ⟨s, abs_le.2 ⟨(hs 0).1.1, (hs 0).1.2⟩, fun n => (hs n).2 n le_rfl⟩

end Woodford.StabilizationWelfare.NonlinearRotembergCentreTools
