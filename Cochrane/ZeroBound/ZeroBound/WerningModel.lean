/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ContinuousTimeNK

/-!
# The Werning (2012) zero-bound model in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2, pp. 474–476,
equations (20.5)–(20.10).

The IS curve and Phillips curve (20.5)–(20.6) are `dx/dt = σ(i − π − u_r)`,
`dπ/dt = ρπ − κ(x + g)`. The experiment: after unexpected news at `t = 0`, the natural rate is
`u_r = u` (the book: `−2%`) on `[0, T)` and `0` afterwards; the nominal rate is `i = 0` on
`[0, T)` and `i = u_r = 0` afterwards; the Phillips-curve disturbance is `g` on `[0, T)` and `0`
afterwards (`g = 0` in §20.2.2, used in §20.2.5). Paths are deterministic `ℝ → ℝ`, continuous
on `[0, ∞)`, satisfying the ODEs by `HasDerivAt` off a countable set (here `{T}`, where the
forcing jumps). Survey error E6: with piecewise-constant `g`, `dg/dt` in (20.9) is a measure
(Dirac masses at `0` and `T`); we solve piecewise, with `x` and `π` continuous at `T` (the jump
conditions), and separately prove (20.8) for continuous forcing on the whole line and its
Stieltjes reading for the experiment.

## Main results

* `IsPath` (20.5)–(20.6); linearity (`IsPath.add`, `IsPath.sub`); `homog_bdd`: bounded
  solutions of the unforced system are `π_t = e^{−λ^b t}π_0`, `κx = λ^f π` (the forward-explosive
  root `C_f e^{λ^f t}` is ruled out, p. 475).
* The closed-form family `wPi`, `wX` indexed by `π_T`; `wPath_isPath`, `wPath_bdd`;
  **`bdd_path_iff`**: the bounded paths of the experiment are exactly this one-parameter family;
  `bdd_path_existsUnique` (the constant is `π_T`); `wPi_shift` (members differ by
  `(π_T − π_T')e^{λ^b(T−t)}`).
* Jump conditions at `T`: `jump_pi`, `jump_x` (`π̇(T⁺) − π̇(T⁻) = κ g`, `ẋ(T⁺) − ẋ(T⁻) = σ u`).
* (20.8)–(20.10) for continuous forcing on the whole line: `eq20_8_solves`, `eq20_8_iff` (both
  directions; `z = κσ(i − u_r) + κ dg/dt`, (20.9)), `family_equiv` (`ℝ ≃` the forward-stable
  solutions, via `C`).
* The Stieltjes reading of (20.8)/(20.10) for the experiment (E6): `experiment_eq20_8`.
* (20.7): `eq20_7_selects` — after `T`, an active rule `i = i* + φ(π − π*)`, `φ > 1`, selects the
  chosen path as the unique bounded one.
-/

namespace Cochrane.ZeroBound.WerningModel

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK

/-! ## The model (20.5)–(20.6) -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474: `(x, π)` is a path of the continuous-time model
with interest rate `i`, natural rate `u` and Phillips-curve disturbance `g`: both continuous on
`[0, ∞)`, and for `t > 0` off the countable set `S` (the dates where the forcing jumps)
`dx/dt = σ(i − π − u)` and `dπ/dt = ρπ − κ(x + g)`. -/
def IsPath (σ ρ κ : ℝ) (i u g : ℝ → ℝ) (S : Set ℝ) (x π : ℝ → ℝ) : Prop :=
  ContinuousOn x (Set.Ici 0) ∧ ContinuousOn π (Set.Ici 0) ∧
    ∀ t, 0 < t → t ∉ S → HasDerivAt x (σ * (i t - π t - u t)) t ∧
      HasDerivAt π (ρ * π t - κ * (x t + g t)) t

/-- Cochrane (2023), §20.2.2, p. 474 ("do not explode as time increases"): bounded on
`[0, ∞)`. -/
def BddOnIci (f : ℝ → ℝ) : Prop := ∃ K, ∀ t, 0 ≤ t → |f t| ≤ K

/-- Cochrane (2023), (20.5)–(20.6), p. 474: the model is linear — sums of paths are paths for
the summed forcing. -/
theorem IsPath.add {σ ρ κ : ℝ} {i u g i' u' g' x π x' π' : ℝ → ℝ} {S S' : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (h' : IsPath σ ρ κ i' u' g' S' x' π') :
    IsPath σ ρ κ (fun t => i t + i' t) (fun t => u t + u' t) (fun t => g t + g' t) (S ∪ S')
      (fun t => x t + x' t) (fun t => π t + π' t) := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, fun t ht hS => ?_⟩
  have hS1 : t ∉ S := fun hh => hS (Or.inl hh)
  have hS2 : t ∉ S' := fun hh => hS (Or.inr hh)
  obtain ⟨a1, b1⟩ := h.2.2 t ht hS1
  obtain ⟨a2, b2⟩ := h'.2.2 t ht hS2
  exact ⟨(a1.add a2).congr_deriv (by ring), (b1.add b2).congr_deriv (by ring)⟩

/-- Cochrane (2023), (20.5)–(20.6), p. 474: the difference of two paths with the same forcing
solves the unforced model. -/
theorem IsPath.sub {σ ρ κ : ℝ} {i u g x π x' π' : ℝ → ℝ} {S S' : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (h' : IsPath σ ρ κ i u g S' x' π') :
    IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (fun _ => 0) (S ∪ S')
      (fun t => x t - x' t) (fun t => π t - π' t) := by
  refine ⟨h.1.sub h'.1, h.2.1.sub h'.2.1, fun t ht hS => ?_⟩
  have hS1 : t ∉ S := fun hh => hS (Or.inl hh)
  have hS2 : t ∉ S' := fun hh => hS (Or.inr hh)
  obtain ⟨a1, b1⟩ := h.2.2 t ht hS1
  obtain ⟨a2, b2⟩ := h'.2.2 t ht hS2
  exact ⟨(a1.sub a2).congr_deriv (by ring), (b1.sub b2).congr_deriv (by ring)⟩

/-- Cochrane (2023), (20.5)–(20.6), p. 474: the model only involves the paths on `[0, ∞)`. -/
theorem IsPath.congr {σ ρ κ : ℝ} {i u g x π x' π' : ℝ → ℝ} {S : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (hx : ∀ t, 0 ≤ t → x' t = x t)
    (hπ : ∀ t, 0 ≤ t → π' t = π t) : IsPath σ ρ κ i u g S x' π' := by
  refine ⟨h.1.congr fun t ht => hx t ht, h.2.1.congr fun t ht => hπ t ht, fun t ht hS => ?_⟩
  have evx : x =ᶠ[𝓝 t] x' := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hx s hs.le).symm
  have evπ : π =ᶠ[𝓝 t] π' := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hπ s hs.le).symm
  obtain ⟨a, b⟩ := h.2.2 t ht hS
  rw [hx t ht.le, hπ t ht.le]
  exact ⟨a.congr_of_eventuallyEq evx.symm, b.congr_of_eventuallyEq evπ.symm⟩

/-- Cochrane (2023), §20.2.2, p. 475 ("we set to zero … forward-explosive equilibria
`C_f e^{λ^f t}`"): **bounded solutions of the unforced model.** If `(x, π)` solves the model with
`i = u = g = 0` (off a countable set) and both are bounded on `[0, ∞)`, then
`π_t = e^{−λ^b t} π_0` and `κ x_t = λ^f π_t` for all `t ≥ 0`. -/
theorem homog_bdd {σ ρ κ : ℝ} {x π : ℝ → ℝ} {S : Set ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hS : S.Countable)
    (h : IsPath σ ρ κ (fun _ => 0) (fun _ => 0) (fun _ => 0) S x π) (hx : BddOnIci x)
    (hπ : BddOnIci π) :
    ∀ t, 0 ≤ t → π t = Real.exp (-(lamb ρ κ σ * t)) * π 0 ∧ κ * x t = lamf ρ κ σ * π t := by
  obtain ⟨hxc, hπc, hd⟩ := h
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨Kπ, hKπ⟩ := hπ
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hroot := lamf_root (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  -- `y = λ^f π − κ x` satisfies `y' = λ^f y`
  have hy := unstable_bdd_zero (f := fun t => lf * π t - κ * x t) (a := lf) (p := 0)
    (K := lf * Kπ + κ * Kx) hf hS ((continuousOn_const.mul hπc).sub (continuousOn_const.mul hxc))
    (fun t ht hts => by
      obtain ⟨a, b⟩ := hd t ht hts
      refine ((b.const_mul lf).sub (a.const_mul κ)).congr_deriv ?_
      linear_combination (-(π t)) * hroot)
    (fun t ht => by
      calc |lf * π t - κ * x t| ≤ |lf * π t| + |κ * x t| := abs_sub _ _
        _ = lf * |π t| + κ * |x t| := by rw [abs_mul, abs_mul, abs_of_pos hf, abs_of_pos hκ]
        _ ≤ lf * Kπ + κ * Kx := add_le_add (mul_le_mul_of_nonneg_left (hKπ t ht) hf.le)
            (mul_le_mul_of_nonneg_left (hKx t ht) hκ.le))
  have hπsol := linear_ode_Ici (f := π) (a := -lb) (p := 0) hS hπc fun t ht hts => by
    obtain ⟨-, b⟩ := hd t ht hts
    refine b.congr_deriv ?_
    have := hy t ht.le
    linear_combination this - (π t) * hsub
  intro t ht
  refine ⟨?_, ?_⟩
  · rw [hπsol t ht]; ring_nf
  · have := hy t ht
    linarith

/-! ## The experiment: closed-form solutions -/

/-- Cochrane (2023), §20.2.2, p. 474: a step path, `c` on `[0, T)` and `0` from `T` on (the
natural rate `u_r`, and the disturbance `g` of §20.2.5). -/
noncomputable def trapStep (c T t : ℝ) : ℝ := if t < T then c else 0

/-- Cochrane (2023), §20.2.2, p. 475: the function
`h(s) = (λ^f e^{λ^b s} + λ^b e^{−λ^f s})/(λ^f + λ^b)` (`s = T − t` is time to the end of the
trap), written for generic roots. -/
noncomputable def hh (lf lb s : ℝ) : ℝ :=
  (lf * Real.exp (lb * s) + lb * Real.exp (-(lf * s))) / (lf + lb)

/-- Cochrane (2023), §20.2.5, p. 481: the function
`k(s) = (e^{λ^b s} − e^{−λ^f s})/(λ^f + λ^b)`, the response to `g` during the trap. -/
noncomputable def kk (lf lb s : ℝ) : ℝ :=
  (Real.exp (lb * s) - Real.exp (-(lf * s))) / (lf + lb)

/-- Cochrane (2023), §20.2.2, p. 475: inflation during the trap, `s = T − t` before its end,
with forcing `A = i − u_r = −u`, disturbance `g`, and end-of-trap inflation `π_T`:
`π = π_T e^{λ^b s} + A(1 − h(s)) + κ g k(s)`. -/
noncomputable def trapPi (lf lb κ A g πT s : ℝ) : ℝ :=
  πT * Real.exp (lb * s) + A * (1 - hh lf lb s) + κ * g * kk lf lb s

/-- Cochrane (2023), §20.2.2, p. 475: during the trap, `y = λ^f π − κ(x + g)` (the forward
integral of the forcing) equals `λ^b A (1 − e^{−λ^f s}) − κ g e^{−λ^f s}`. -/
noncomputable def trapY (lf lb κ A g s : ℝ) : ℝ :=
  lb * A * (1 - Real.exp (-(lf * s))) - κ * g * Real.exp (-(lf * s))

/-- Cochrane (2023), §20.2.2, pp. 475–476 (Figure 20.4): the inflation path of the
equilibrium indexed by `π_T`: the trap formula on `[0, T]`, `π_T e^{−λ^b(t−T)}` after. -/
noncomputable def wPi (σ κ ρ T u g πT t : ℝ) : ℝ :=
  if t ≤ T then trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t)
  else πT * Real.exp (-(lamb ρ κ σ * (t - T)))

/-- Cochrane (2023), (20.6) and (20.10), p. 475: the output-gap path of the equilibrium indexed
by `π_T`: `x = (λ^f π − y)/κ − g` on `[0, T]` and `x = λ^f π/κ` after. -/
noncomputable def wX (σ κ ρ T u g πT t : ℝ) : ℝ :=
  if t ≤ T then
    (lamf ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t) -
      trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t)) / κ - g
  else lamf ρ κ σ * (πT * Real.exp (-(lamb ρ κ σ * (t - T)))) / κ

/-- Cochrane (2023), §20.2.2, p. 475: `h(0) = 1`. -/
theorem hh_zero {lf lb : ℝ} (h : lf + lb ≠ 0) : hh lf lb 0 = 1 := by
  simp only [hh, mul_zero, neg_zero, Real.exp_zero, mul_one]
  exact div_self h

/-- Cochrane (2023), §20.2.5, p. 481: `k(0) = 0`. -/
theorem kk_zero (lf lb : ℝ) : kk lf lb 0 = 0 := by
  simp [kk]

/-- Cochrane (2023), §20.2.2, p. 475: `h'(s) = λ^f λ^b k(s)`. -/
theorem hh_hasDerivAt {lf lb : ℝ} (h : lf + lb ≠ 0) (s : ℝ) :
    HasDerivAt (hh lf lb) (lf * lb * kk lf lb s) s := by
  have := (((hasDerivAt_expPos lb s).const_mul lf).add
    ((hasDerivAt_expNeg lf s).const_mul lb)).div_const (lf + lb)
  refine this.congr_deriv ?_
  simp only [kk]
  field_simp
  ring

/-- Cochrane (2023), §20.2.5, p. 481: `k'(s) = (λ^b e^{λ^b s} + λ^f e^{−λ^f s})/(λ^f + λ^b)`. -/
theorem kk_hasDerivAt (lf lb s : ℝ) :
    HasDerivAt (kk lf lb)
      ((lb * Real.exp (lb * s) + lf * Real.exp (-(lf * s))) / (lf + lb)) s := by
  have := ((hasDerivAt_expPos lb s).sub (hasDerivAt_expNeg lf s)).div_const (lf + lb)
  refine this.congr_deriv ?_
  ring

/-- Cochrane (2023), §20.2.2, p. 475: in time-to-go `s`, the trap formula satisfies
`dπ/ds = λ^b π − y`. -/
theorem trapPi_hasDerivAt {lf lb κ A g πT : ℝ} (h : lf + lb ≠ 0) (s : ℝ) :
    HasDerivAt (trapPi lf lb κ A g πT)
      (lb * trapPi lf lb κ A g πT s - trapY lf lb κ A g s) s := by
  have := ((((hasDerivAt_expPos lb s).const_mul πT).add
    (((hasDerivAt_const s (1 : ℝ)).sub (hh_hasDerivAt h s)).const_mul A)).add
    ((kk_hasDerivAt lf lb s).const_mul (κ * g)))
  refine this.congr_deriv ?_
  simp only [trapPi, trapY, hh, kk]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `dy/ds = λ^f (λ^b A + κ g) e^{−λ^f s}`. -/
theorem trapY_hasDerivAt (lf lb κ A g s : ℝ) :
    HasDerivAt (trapY lf lb κ A g)
      (lf * (lb * A + κ * g) * Real.exp (-(lf * s))) s := by
  have := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_expNeg lf s)).const_mul (lb * A)).sub
    ((hasDerivAt_expNeg lf s).const_mul (κ * g))
  refine this.congr_deriv ?_
  ring

/-- Cochrane (2023), §20.2.2, p. 475: at the end of the trap the formula gives `π_T`. -/
theorem trapPi_zero {lf lb : ℝ} (h : lf + lb ≠ 0) (κ A g πT : ℝ) :
    trapPi lf lb κ A g πT 0 = πT := by
  simp [trapPi, hh_zero h, kk_zero]

/-- Cochrane (2023), §20.2.2, p. 475: at the end of the trap `y = −κ g`. -/
theorem trapY_zero (lf lb κ A g : ℝ) : trapY lf lb κ A g 0 = -(κ * g) := by
  simp [trapY]

/-- Cochrane (2023), §20.2.2, p. 475: the trap formula is affine in `π_T`. -/
theorem trapPi_shift (lf lb κ A g πT s : ℝ) :
    trapPi lf lb κ A g πT s = trapPi lf lb κ A g 0 s + πT * Real.exp (lb * s) := by
  simp only [trapPi]
  ring

/-- Cochrane (2023), §20.2.2, p. 475: `π_T` is the value of the path at `T`. -/
theorem wPi_T {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT : ℝ) :
    wPi σ κ ρ T u g πT T = πT := by
  simp [wPi, trapPi_zero (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne']

/-- Cochrane (2023), §20.2.2, p. 475 (Figure 20.4): two members of the family differ by
`(π_T − π_T') e^{λ^b(T − t)}` at every date — here, `π(π_T) = π(0) + π_T e^{λ^b(T−t)}`. -/
theorem wPi_shift (σ κ ρ T u g πT t : ℝ) :
    wPi σ κ ρ T u g πT t = wPi σ κ ρ T u g 0 t + πT * Real.exp (lamb ρ κ σ * (T - t)) := by
  unfold wPi
  split_ifs
  · rw [trapPi_shift]
  · have : -(lamb ρ κ σ * (t - T)) = lamb ρ κ σ * (T - t) := by ring
    rw [this]
    ring

/-- Cochrane (2023), (20.10), p. 475: the output gaps of two members differ by
`λ^f(π_T − π_T') e^{λ^b(T−t)}/κ`. -/
theorem wX_shift (σ κ ρ T u g πT t : ℝ) :
    wX σ κ ρ T u g πT t =
      wX σ κ ρ T u g 0 t + lamf ρ κ σ * (πT * Real.exp (lamb ρ κ σ * (T - t))) / κ := by
  unfold wX
  split_ifs
  · rw [trapPi_shift]
    ring
  · have : -(lamb ρ κ σ * (t - T)) = lamb ρ κ σ * (T - t) := by ring
    rw [this]
    ring

/-- Cochrane (2023), §20.2.2, p. 475: the inflation path is continuous. -/
theorem wPi_continuous (σ κ ρ T u g πT : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    Continuous (wPi σ κ ρ T u g πT) := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have h1 : Continuous fun t => trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t) := by
    unfold trapPi hh kk
    fun_prop (disch := exact hne)
  have h2 : Continuous fun t => πT * Real.exp (-(lamb ρ κ σ * (t - T))) := by fun_prop
  exact Continuous.if_le (f := fun t => t) (g := fun _ => T) h1 h2 continuous_id
    continuous_const fun t (ht : t = T) => by
      subst ht
      rw [sub_self, trapPi_zero hne]
      simp

/-- Cochrane (2023), (20.10), p. 475: the output-gap path is continuous (`x` does not jump at
`T`). -/
theorem wX_continuous (σ κ ρ T u g πT : ℝ) (hκ : 0 < κ) (hσ : 0 < σ) :
    Continuous (wX σ κ ρ T u g πT) := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have h1 : Continuous fun t => (lamf ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT
      (T - t) - trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t)) / κ - g := by
    unfold trapPi trapY hh kk
    fun_prop (disch := exact hne)
  have h2 : Continuous fun t =>
      lamf ρ κ σ * (πT * Real.exp (-(lamb ρ κ σ * (t - T)))) / κ := by fun_prop
  exact Continuous.if_le (f := fun t => t) (g := fun _ => T) h1 h2 continuous_id
    continuous_const fun t (ht : t = T) => by
      subst ht
      rw [sub_self, trapPi_zero hne, trapY_zero]
      field_simp
      simp

/-- Cochrane (2023), (20.5)–(20.6), p. 474: **every member of the family is a path of the
experiment** (`i = 0`, `u_r = u` then `0`, `g` then `0`; the ODEs hold off `{T}`). -/
theorem wPath_isPath {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT : ℝ) :
    IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T}
      (wX σ κ ρ T u g πT) (wPi σ κ ρ T u g πT) := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  refine ⟨(wX_continuous σ κ ρ T u g πT hκ hσ).continuousOn,
    (wPi_continuous σ κ ρ T u g πT hκ hσ).continuousOn, fun t _ hT => ?_⟩
  have hT' : t ≠ T := hT
  set lf := lamf ρ κ σ
  set lb := lamb ρ κ σ
  rcases lt_or_gt_of_ne hT' with hlt | hgt
  · -- during the trap
    have evπ : wPi σ κ ρ T u g πT =ᶠ[𝓝 t]
        fun s => trapPi lf lb κ (-u) g πT (T - s) := by
      filter_upwards [Iio_mem_nhds hlt] with s (hs : s < T)
      simp [wPi, le_of_lt hs, lf, lb]
    have evx : wX σ κ ρ T u g πT =ᶠ[𝓝 t]
        fun s => (lf * trapPi lf lb κ (-u) g πT (T - s) -
          trapY lf lb κ (-u) g (T - s)) / κ - g := by
      filter_upwards [Iio_mem_nhds hlt] with s (hs : s < T)
      simp [wX, le_of_lt hs, lf, lb]
    have hP := (trapPi_hasDerivAt (κ := κ) (A := -u) (g := g) (πT := πT) hne (T - t)).comp t
      ((hasDerivAt_id t).const_sub T)
    have hY := (trapY_hasDerivAt lf lb κ (-u) g (T - t)).comp t ((hasDerivAt_id t).const_sub T)
    have hπv : wPi σ κ ρ T u g πT t = trapPi lf lb κ (-u) g πT (T - t) := evπ.eq_of_nhds
    have hxv : wX σ κ ρ T u g πT t = (lf * trapPi lf lb κ (-u) g πT (T - t) -
        trapY lf lb κ (-u) g (T - t)) / κ - g := evx.eq_of_nhds
    have hst : trapStep u T t = u := by simp [trapStep, hlt]
    have hgt' : trapStep g T t = g := by simp [trapStep, hlt]
    rw [hst, hgt', hπv, hxv]
    refine ⟨?_, ?_⟩
    · refine (((hP.const_mul lf).sub hY).div_const κ |>.sub_const g).congr_of_eventuallyEq
        evx |>.congr_deriv ?_
      simp only [trapY]
      field_simp
      linear_combination (-u - trapPi lf lb κ (-u) g πT (T - t)) * hmul
    · refine (hP.congr_of_eventuallyEq evπ).congr_deriv ?_
      field_simp
      linear_combination (trapPi lf lb κ (-u) g πT (T - t)) * hsub
  · -- after the trap
    have evπ : wPi σ κ ρ T u g πT =ᶠ[𝓝 t] fun s => πT * Real.exp (-(lb * (s - T))) := by
      filter_upwards [Ioi_mem_nhds hgt] with s (hs : T < s)
      simp [wPi, not_le.2 hs, lb]
    have evx : wX σ κ ρ T u g πT =ᶠ[𝓝 t]
        fun s => lf * (πT * Real.exp (-(lb * (s - T)))) / κ := by
      filter_upwards [Ioi_mem_nhds hgt] with s (hs : T < s)
      simp [wX, not_le.2 hs, lf, lb]
    have hE : HasDerivAt (fun s => πT * Real.exp (-(lb * (s - T))))
        (πT * (-lb * Real.exp (-(lb * (t - T))))) t := by
      have := ((hasDerivAt_expNeg lb (t - T)).comp t ((hasDerivAt_id t).sub_const T)).const_mul πT
      simpa [Function.comp] using this
    have hst : trapStep u T t = 0 := by simp [trapStep, not_lt.2 hgt.le]
    have hgt' : trapStep g T t = 0 := by simp [trapStep, not_lt.2 hgt.le]
    rw [hst, hgt', evπ.eq_of_nhds, evx.eq_of_nhds]
    refine ⟨?_, ?_⟩
    · refine ((hE.const_mul lf).div_const κ).congr_of_eventuallyEq evx |>.congr_deriv ?_
      field_simp
      linear_combination (-(πT * Real.exp (-(lb * (t - T))))) * hmul
    · refine (hE.congr_of_eventuallyEq evπ).congr_deriv ?_
      field_simp
      linear_combination (πT * Real.exp (-(lb * (t - T)))) * hsub

/-- Cochrane (2023), §20.2.2, p. 474: a continuous path that is `c e^{−λ^b(t−T)}` after `T` is
bounded on `[0, ∞)`. -/
theorem bdd_of_cont_exp {f : ℝ → ℝ} {T c b : ℝ} (hf : Continuous f) (hb : 0 ≤ b)
    (hafter : ∀ t, T < t → f t = c * Real.exp (-(b * (t - T)))) : BddOnIci f := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C |c|, fun t ht => ?_⟩
  rcases le_or_gt t T with h | h
  · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
  · rw [hafter t h, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine le_trans ?_ (le_max_right _ _)
    refine mul_le_of_le_one_right (abs_nonneg c) ?_
    rw [Real.exp_le_one_iff]
    nlinarith

/-- Cochrane (2023), §20.2.2, p. 474: **every member of the family is bounded** ("does not
explode as time increases"). -/
theorem wPath_bdd {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT : ℝ) :
    BddOnIci (wX σ κ ρ T u g πT) ∧ BddOnIci (wPi σ κ ρ T u g πT) := by
  have hb := (lamb_pos (ρ := ρ) hκ hσ).le
  refine ⟨bdd_of_cont_exp (c := lamf ρ κ σ * πT / κ) (T := T)
      (wX_continuous σ κ ρ T u g πT hκ hσ) hb fun t ht => ?_,
    bdd_of_cont_exp (c := πT) (T := T) (wPi_continuous σ κ ρ T u g πT hκ hσ) hb fun t ht => ?_⟩
  · simp only [wX, not_le.2 ht, ↓reduceIte]
    ring
  · simp [wPi, not_le.2 ht]

/-- Cochrane (2023), §20.2.2, pp. 474–475: **the bounded paths of the experiment are exactly
the one-parameter family indexed by `π_T`** (Figure 20.4). For `σ, κ > 0`, `(x, π)` is a path
(20.5)–(20.6) with `i = 0`, `u_r = u` on `[0,T)` and `0` after, `g` on `[0,T)` and `0` after,
bounded on `[0, ∞)`, iff for some `π_T` it equals `(wX π_T, wPi π_T)` on `[0, ∞)`. -/
theorem bdd_path_iff {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) {x π : ℝ → ℝ} :
    (IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
        BddOnIci π) ↔
      ∃ πT, ∀ t, 0 ≤ t → π t = wPi σ κ ρ T u g πT t ∧ x t = wX σ κ ρ T u g πT t := by
  constructor
  · rintro ⟨hp, ⟨Kx, hKx⟩, ⟨Kπ, hKπ⟩⟩
    obtain ⟨⟨Kx0, hKx0⟩, ⟨Kπ0, hKπ0⟩⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g 0
    have hd := hp.sub (wPath_isPath (ρ := ρ) hκ hσ T u g 0)
    have hh := homog_bdd hσ hκ ((Set.countable_singleton T).union (Set.countable_singleton T))
      hd ⟨Kx + Kx0, fun t ht => (abs_sub _ _).trans (add_le_add (hKx t ht) (hKx0 t ht))⟩
      ⟨Kπ + Kπ0, fun t ht => (abs_sub _ _).trans (add_le_add (hKπ t ht) (hKπ0 t ht))⟩
    set D := π 0 - wPi σ κ ρ T u g 0 0
    refine ⟨Real.exp (-(lamb ρ κ σ * T)) * D, fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := hh t ht
    have he : Real.exp (-(lamb ρ κ σ * T)) * D * Real.exp (lamb ρ κ σ * (T - t)) =
        Real.exp (-(lamb ρ κ σ * t)) * D := by
      rw [mul_comm _ D, mul_assoc, ← Real.exp_add]; ring_nf
    rw [wPi_shift, wX_shift, he]
    refine ⟨by linarith, ?_⟩
    rw [← h1]
    field_simp
    linarith
  · rintro ⟨πT, h⟩
    obtain ⟨hx, hπ⟩ := wPath_bdd (ρ := ρ) hκ hσ T u g πT
    refine ⟨(wPath_isPath (ρ := ρ) hκ hσ T u g πT).congr (fun t ht => (h t ht).2)
      (fun t ht => (h t ht).1), ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hx
      exact ⟨K, fun t ht => by rw [(h t ht).2]; exact hK t ht⟩
    · obtain ⟨K, hK⟩ := hπ
      exact ⟨K, fun t ht => by rw [(h t ht).1]; exact hK t ht⟩

/-- Cochrane (2023), §20.2.2, p. 475: **the free constant is unique**: a bounded path of the
experiment equals exactly one member of the family (its constant is `π_T`). -/
theorem bdd_path_existsUnique {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hT : 0 ≤ T)
    {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    ∃! πT, ∀ t, 0 ≤ t → π t = wPi σ κ ρ T u g πT t ∧ x t = wX σ κ ρ T u g πT t := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  refine ⟨πT, hπT, fun πT' h' => ?_⟩
  have a := (h' T hT).1
  have b := (hπT T hT).1
  rw [wPi_T hκ hσ] at a b
  rw [← a, b]

/-! ### Jump conditions at `T` -/

/-- Cochrane (2023), §20.2.2, p. 475: the trap branch of the inflation path has derivative
`−(λ^b π − y)` in calendar time. -/
theorem trapBranch_hasDerivAt {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT t : ℝ) :
    HasDerivAt (fun s => trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - s))
      (-(lamb ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t) -
        trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t))) t := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hP := (trapPi_hasDerivAt (κ := κ) (A := -u) (g := g) (πT := πT) hne (T - t)).comp t
    ((hasDerivAt_id t).const_sub T)
  exact hP.congr_deriv (by ring)

/-- Cochrane (2023), §20.2.2, p. 475: the trap branch of the output-gap path has derivative
`σ(A − π)` in calendar time. -/
theorem trapBranchX_hasDerivAt {σ κ ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (T u g πT t : ℝ) :
    HasDerivAt (fun s => (lamf ρ κ σ * trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - s) -
        trapY (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - s)) / κ - g)
      (σ * (-u - trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t))) t := by
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hP := trapBranch_hasDerivAt (ρ := ρ) hκ hσ T u g πT t
  have hY := (trapY_hasDerivAt (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g (T - t)).comp t
    ((hasDerivAt_id t).const_sub T)
  refine (((hP.const_mul (lamf ρ κ σ)).sub hY).div_const κ |>.sub_const g).congr_deriv ?_
  simp only [trapY]
  field_simp
  linear_combination (-u - trapPi (lamf ρ κ σ) (lamb ρ κ σ) κ (-u) g πT (T - t)) * hmul

/-- Cochrane (2023), §20.2.2, p. 475: the post-trap branch `π_T e^{−λ^b(t−T)}` has derivative
`−λ^b` times itself. -/
theorem postBranch_hasDerivAt (b T c t : ℝ) :
    HasDerivAt (fun s => c * Real.exp (-(b * (s - T))))
      (-b * (c * Real.exp (-(b * (t - T))))) t := by
  have := ((hasDerivAt_expNeg b (t - T)).comp t ((hasDerivAt_id t).sub_const T)).const_mul c
  refine this.congr_deriv ?_
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (survey E6: the jump conditions): along any bounded path of
the experiment, `π` is continuous at `T` and its one-sided derivatives there are
`π̇(T⁻) = ρπ_T − κ(x_T + g)` and `π̇(T⁺) = ρπ_T − κ x_T`, so `π̇(T⁺) − π̇(T⁻) = κ g`
(`= κ(g(T⁻) − g(T⁺))`). -/
theorem jump_pi {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hT : 0 ≤ T) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    HasDerivWithinAt π (ρ * π T - κ * (x T + g)) (Set.Icc 0 T) T ∧
      HasDerivWithinAt π (ρ * π T - κ * (x T + 0)) (Set.Ici T) T := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hsub := lamf_sub_lamb ρ κ σ
  have hxT : x T = lamf ρ κ σ * πT / κ := by
    rw [(hπT T hT).2]
    simp [wX, trapPi_zero hne, trapY_zero]
    field_simp
    ring
  have hπTv : π T = πT := by rw [(hπT T hT).1, wPi_T hκ hσ]
  refine ⟨?_, ?_⟩
  · have hd := (trapBranch_hasDerivAt (ρ := ρ) hκ hσ T u g πT T).hasDerivWithinAt
      (s := Set.Icc 0 T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t ht.1).1]
      simp [wPi, ht.2]
    · rw [(hπT T hT).1]
      simp [wPi]
    · rw [sub_self, trapPi_zero hne, trapY_zero, hπTv, hxT]
      field_simp
      linear_combination πT * hsub
  · have hd := (postBranch_hasDerivAt (lamb ρ κ σ) T πT T).hasDerivWithinAt (s := Set.Ici T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t (le_trans hT ht)).1]
      rcases eq_or_lt_of_le (Set.mem_Ici.1 ht) with h | h
      · subst h
        simp [wPi, trapPi_zero hne]
      · simp [wPi, not_le.2 h]
    · rw [(hπT T hT).1]
      simp [wPi, trapPi_zero hne]
    · rw [hπTv, hxT]
      simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      field_simp
      linear_combination πT * hsub

/-- Cochrane (2023), §20.2.2, p. 475 (the jump conditions): along any bounded path, `x` is
continuous at `T`, `ẋ(T⁻) = σ(0 − π_T − u)` and `ẋ(T⁺) = σ(0 − π_T − 0)`, so
`ẋ(T⁺) − ẋ(T⁻) = σ u` (the natural rate jumps from `u` to `0`). -/
theorem jump_x {σ κ ρ T u g : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hT : 0 ≤ T) {x π : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) :
    HasDerivWithinAt x (σ * (0 - π T - u)) (Set.Icc 0 T) T ∧
      HasDerivWithinAt x (σ * (0 - π T - 0)) (Set.Ici T) T := by
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hπTv : π T = πT := by rw [(hπT T hT).1, wPi_T hκ hσ]
  refine ⟨?_, ?_⟩
  · have hd := (trapBranchX_hasDerivAt (ρ := ρ) hκ hσ T u g πT T).hasDerivWithinAt
      (s := Set.Icc 0 T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t ht.1).2]
      simp [wX, ht.2]
    · rw [(hπT T hT).2]
      simp [wX]
    · rw [sub_self, trapPi_zero hne, hπTv]
      ring
  · have hd := ((postBranch_hasDerivAt (lamb ρ κ σ) T πT T).const_mul (lamf ρ κ σ)).div_const κ
      |>.hasDerivWithinAt (s := Set.Ici T)
    refine (hd.congr (fun t ht => ?_) ?_).congr_deriv ?_
    · rw [(hπT t (le_trans hT ht)).2]
      rcases eq_or_lt_of_le (Set.mem_Ici.1 ht) with h | h
      · subst h
        simp [wX, trapPi_zero hne, trapY_zero]
        field_simp
        ring
      · simp [wX, not_le.2 h]
    · rw [(hπT T hT).2]
      simp [wX, trapPi_zero hne, trapY_zero]
      field_simp
      ring
    · rw [hπTv]
      simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
      field_simp
      linear_combination (-πT) * hmul

/-! ## (20.8)–(20.10) for continuous forcing on the whole line -/

/-- Cochrane (2023), (20.5)–(20.6), p. 474, on the whole time line: `x`, `π` differentiable at
every date with `ẋ = σ(i − π − u)`, `π̇ = ρπ − κ(x + g)`. -/
def IsGlobalSol (σ ρ κ : ℝ) (i u g x π : ℝ → ℝ) : Prop :=
  ∀ t, HasDerivAt x (σ * (i t - π t - u t)) t ∧ HasDerivAt π (ρ * π t - κ * (x t + g t)) t

/-- Cochrane (2023), (20.9), p. 475 (survey E6: `r_t` there is the natural rate `u_{r,t}`):
the forcing `z = κσ(i − u_r) + κ dg/dt`, with `g'` the derivative of `g`. -/
noncomputable def zForce (σ κ : ℝ) (i u g' : ℝ → ℝ) (t : ℝ) : ℝ :=
  κ * σ * (i t - u t) + κ * g' t

/-- Cochrane (2023), (20.10), p. 475: the output gap of the member with constant `C`,
`κx = −κg + λ^f C e^{−λ^b t} + (λ^f + λ^b)⁻¹[λ^f ∫_{−∞}^t … − λ^b ∫_t^∞ …]`. -/
noncomputable def bookX (σ κ ρ : ℝ) (g z : ℝ → ℝ) (C t : ℝ) : ℝ :=
  (-(κ * g t) + lamf ρ κ σ * C * Real.exp (-(lamb ρ κ σ * t)) +
    (lamf ρ κ σ * bwdInfInt (lamb ρ κ σ) z t - lamb ρ κ σ * fwdInt (lamf ρ κ σ) z t) /
      (lamf ρ κ σ + lamb ρ κ σ)) / κ

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475: **every member of the family solves the
model**: for each `C`, `(x, π) = ((20.10), (20.8))` satisfies (20.5)–(20.6) at every date
(continuous `i`, `u`; differentiable `g` with continuous derivative; bounded forcing (20.9)). -/
theorem eq20_8_solves {σ κ ρ M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {i u g g' : ℝ → ℝ}
    (hi : Continuous i) (hu : Continuous u) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hM : ∀ s, |zForce σ κ i u g' s| ≤ M) (C : ℝ) :
    IsGlobalSol σ ρ κ i u g (bookX σ κ ρ g (zForce σ κ i u g') C)
      (greenPi (lamf ρ κ σ) (lamb ρ κ σ) (zForce σ κ i u g') C) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hz : Continuous (zForce σ κ i u g') := by unfold zForce; fun_prop
  set z := zForce σ κ i u g' with hzdef
  intro t
  have hB := bwdInfInt_hasDerivAt hb hz hM t
  have hF := fwdInt_hasDerivAt hf hz hM t
  refine ⟨?_, ?_⟩
  · have := (((((hg t).const_mul κ).neg.add ((hasDerivAt_expNeg (lamb ρ κ σ) t).const_mul
      (lamf ρ κ σ * C))).add (((hB.const_mul (lamf ρ κ σ)).sub
        (hF.const_mul (lamb ρ κ σ))).div_const (lamf ρ κ σ + lamb ρ κ σ))).div_const κ)
    refine this.congr_deriv ?_
    simp only [greenPi, hzdef, zForce]
    field_simp
    linear_combination (-(C * Real.exp (-(lamb ρ κ σ * t)) * (lamf ρ κ σ + lamb ρ κ σ)) -
      (bwdInfInt (lamb ρ κ σ) z t + fwdInt (lamf ρ κ σ) z t)) * hmul
  · have key : κ * bookX σ κ ρ g z C t = -(κ * g t) +
        lamf ρ κ σ * greenPi (lamf ρ κ σ) (lamb ρ κ σ) z C t - fwdInt (lamf ρ κ σ) z t := by
      simp only [bookX, greenPi]
      field_simp
      ring
    refine (greenPi_hasDerivAt hf hb hz hM t).congr_deriv ?_
    linear_combination key + greenPi (lamf ρ κ σ) (lamb ρ κ σ) z C t * hsub

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475: **the forward-stable solutions are exactly the
family (20.8)–(20.10)** (both directions). For a solution of (20.5)–(20.6) at every date (with
continuous `i`, `u`, differentiable `g` with continuous derivative, and bounded forcing (20.9)),
`e^{−λ^f t}π_t → 0` (no forward explosion) iff `π` is (20.8) and `x` is (20.10) for some `C`. -/
theorem eq20_8_iff {σ κ ρ M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {i u g g' x π : ℝ → ℝ}
    (hi : Continuous i) (hu : Continuous u) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hM : ∀ s, |zForce σ κ i u g' s| ≤ M)
    (h : IsGlobalSol σ ρ κ i u g x π) :
    Tendsto (fun t => Real.exp (-(lamf ρ κ σ * t)) * π t) atTop (𝓝 0) ↔
      ∃ C, π = greenPi (lamf ρ κ σ) (lamb ρ κ σ) (zForce σ κ i u g') C ∧
        x = bookX σ κ ρ g (zForce σ κ i u g') C := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hroot := lamf_root (ρ := ρ) hκ hσ
  have hsub := lamf_sub_lamb ρ κ σ
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hz : Continuous (zForce σ κ i u g') := by unfold zForce; fun_prop
  set z := zForce σ κ i u g' with hzdef
  set y : ℝ → ℝ := fun t => lamf ρ κ σ * π t - κ * (x t + g t) with hy
  have hπd : ∀ t, HasDerivAt π (-lamb ρ κ σ * π t + y t) t := fun t =>
    (h t).2.congr_deriv (by simp only [hy]; linear_combination (-(π t)) * hsub)
  have hyd : ∀ t, HasDerivAt y (lamf ρ κ σ * y t - z t) t := fun t => by
    have := (((h t).2.const_mul (lamf ρ κ σ)).sub (((h t).1.add (hg t)).const_mul κ))
    refine this.congr_deriv ?_
    simp only [hy, hzdef, zForce]
    linear_combination (-(π t)) * hroot
  rw [forward_stable_iff hf hb hz hM hπd hyd]
  constructor
  · rintro ⟨C, hC, hyF⟩
    refine ⟨C, hC, funext fun t => ?_⟩
    have hyt := congrFun hyF t
    simp only [hy] at hyt
    have hπt := congrFun hC t
    have key : κ * bookX σ κ ρ g z C t = -(κ * g t) +
        lamf ρ κ σ * greenPi (lamf ρ κ σ) (lamb ρ κ σ) z C t - fwdInt (lamf ρ κ σ) z t := by
      simp only [bookX, greenPi]
      field_simp
      ring
    apply mul_left_cancel₀ hκ.ne'
    rw [key, ← hπt]
    linarith
  · rintro ⟨C, hC, hx⟩
    refine ⟨C, hC, funext fun t => ?_⟩
    simp only [hy, congrFun hx t, congrFun hC t, bookX, greenPi]
    field_simp
    ring

/-- Cochrane (2023), §20.2.2, p. 475 ("multiple forward-stable equilibrium inflation paths,
indexed by the free constant `C`"): **the forward-stable solutions are in bijection with `ℝ`
via `C`.** -/
noncomputable def family_equiv {σ κ ρ M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {i u g g' : ℝ → ℝ}
    (hi : Continuous i) (hu : Continuous u) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg' : Continuous g') (hM : ∀ s, |zForce σ κ i u g' s| ≤ M) :
    ℝ ≃ {p : (ℝ → ℝ) × (ℝ → ℝ) // IsGlobalSol σ ρ κ i u g p.1 p.2 ∧
      Tendsto (fun t => Real.exp (-(lamf ρ κ σ * t)) * p.2 t) atTop (𝓝 0)} where
  toFun C := ⟨(bookX σ κ ρ g (zForce σ κ i u g') C,
      greenPi (lamf ρ κ σ) (lamb ρ κ σ) (zForce σ κ i u g') C),
    eq20_8_solves hσ hκ hi hu hg hg' hM C,
    greenPi_forward_stable (lamf_pos hκ hσ) (lamb_pos hκ hσ) hM⟩
  invFun p := p.1.2 0 - (bwdInfInt (lamb ρ κ σ) (zForce σ κ i u g') 0 +
    fwdInt (lamf ρ κ σ) (zForce σ κ i u g') 0) / (lamf ρ κ σ + lamb ρ κ σ)
  left_inv C := by
    simp [greenPi]
  right_inv p := by
    obtain ⟨⟨x, π⟩, hsol, hst⟩ := p
    obtain ⟨C, hC, hx⟩ := (eq20_8_iff hσ hκ hi hu hg hg' hM hsol).1 hst
    subst hC hx
    simp [greenPi]

/-! ## The Stieltjes reading of (20.8)–(20.10) for the experiment (survey E6) -/

/-- Cochrane (2023), (20.8), p. 474: the Green's kernel of (20.8),
`K(t, s) = e^{−λ^b(t−s)}` for `s ≤ t` and `e^{−λ^f(s−t)}` for `s > t`. -/
noncomputable def kern (lf lb t s : ℝ) : ℝ :=
  if s ≤ t then Real.exp (-(lb * (t - s))) else Real.exp (-(lf * (s - t)))

/-- Cochrane (2023), (20.9), p. 475, in the experiment (`i = 0`): the absolutely continuous part
of the forcing, `κσ(i − u_r)`. -/
noncomputable def zTrap (σ κ u T s : ℝ) : ℝ := κ * σ * (0 - trapStep u T s)

/-- Cochrane (2023), (20.8), p. 474: `∫_p^q c e^{−b(t−s)} ds = c(e^{−b(t−q)} − e^{−b(t−p)})/b`. -/
theorem integral_exp_bwd {b : ℝ} (hb : b ≠ 0) (c t p q : ℝ) :
    ∫ s in p..q, c * Real.exp (-(b * (t - s))) =
      c * (Real.exp (-(b * (t - q))) - Real.exp (-(b * (t - p)))) / b := by
  have hd : ∀ s ∈ Set.uIcc p q, HasDerivAt (fun s => c * Real.exp (-(b * (t - s))) / b)
      (c * Real.exp (-(b * (t - s)))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(b * (t - s))) b s := by
      have := ((hasDerivAt_id s).const_sub t).const_mul b |>.neg
      refine this.congr_deriv ?_
      ring
    have := ((h1.exp).const_mul c).div_const b
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => c * Real.exp (-(b * (t - s)))).intervalIntegrable
      p q)]
  ring

/-- Cochrane (2023), (20.8), p. 474: `∫_p^q c e^{−a(s−t)} ds = c(e^{−a(p−t)} − e^{−a(q−t)})/a`. -/
theorem integral_exp_fwd {a : ℝ} (ha : a ≠ 0) (c t p q : ℝ) :
    ∫ s in p..q, c * Real.exp (-(a * (s - t))) =
      c * (Real.exp (-(a * (p - t))) - Real.exp (-(a * (q - t)))) / a := by
  have hd : ∀ s ∈ Set.uIcc p q, HasDerivAt (fun s => -(c * Real.exp (-(a * (s - t)))) / a)
      (c * Real.exp (-(a * (s - t)))) s := by
    intro s _
    have := (((hasDerivAt_expNeg a (s - t)).comp s ((hasDerivAt_id s).sub_const t)).const_mul
      c).neg.div_const a
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun s : ℝ => c * Real.exp (-(a * (s - t)))).intervalIntegrable
      p q)]
  ring

/-- Cochrane (2023), (20.8), p. 474, the backward integral in the trap (`0 ≤ t ≤ T`):
`∫_0^t e^{−b(t−s)} z_s ds = c(1 − e^{−bt})/b` for `z = c` on `[0, T)`. -/
theorem bwd_step_le {b c T t : ℝ} (hb : b ≠ 0) (ht : 0 ≤ t) (htT : t ≤ T) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(b * (t - s))) * trapStep c T s =
      c * (1 - Real.exp (-(b * t))) / b := by
  have h : ∫ s in (0 : ℝ)..t, Real.exp (-(b * (t - s))) * trapStep c T s =
      ∫ s in (0 : ℝ)..t, c * Real.exp (-(b * (t - s))) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume T] with s hs hmem
    rw [Set.uIoc_of_le ht] at hmem
    have : s < T := lt_of_le_of_ne (le_trans hmem.2 htT) hs
    simp [trapStep, this, mul_comm]
  rw [h, integral_exp_bwd hb]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero]

/-- Cochrane (2023), (20.8), p. 474, the backward integral after the trap (`0 ≤ T ≤ t`):
`∫_0^t e^{−b(t−s)} z_s ds = c(e^{−b(t−T)} − e^{−bt})/b`. -/
theorem bwd_step_ge {b c T t : ℝ} (hb : b ≠ 0) (hT : 0 ≤ T) (htT : T ≤ t) :
    ∫ s in (0 : ℝ)..t, Real.exp (-(b * (t - s))) * trapStep c T s =
      c * (Real.exp (-(b * (t - T))) - Real.exp (-(b * t))) / b := by
  have hind : (fun s => Real.exp (-(b * (t - s))) * trapStep c T s) =
      (Set.Iio T).indicator fun s => c * Real.exp (-(b * (t - s))) := by
    funext s
    by_cases hs : s < T
    · simp [trapStep, hs, Set.indicator, mul_comm]
    · simp [trapStep, hs, Set.indicator]
  rw [intervalIntegral.integral_of_le (le_trans hT htT), hind,
    setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioc 0 t ∩ Set.Iio T = Set.Ioo 0 T := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
  rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT,
    integral_exp_bwd hb]
  simp only [sub_zero]

/-- Cochrane (2023), (20.8), p. 474, the forward integral in the trap (`t ≤ T`):
`∫_t^∞ e^{−a(s−t)} z_s ds = c(1 − e^{−a(T−t)})/a`. -/
theorem fwd_step_le {a c T t : ℝ} (ha : a ≠ 0) (htT : t ≤ T) :
    ∫ s in Set.Ioi t, Real.exp (-(a * (s - t))) * trapStep c T s =
      c * (1 - Real.exp (-(a * (T - t)))) / a := by
  have hind : (fun s => Real.exp (-(a * (s - t))) * trapStep c T s) =
      (Set.Iio T).indicator fun s => c * Real.exp (-(a * (s - t))) := by
    funext s
    by_cases hs : s < T
    · simp [trapStep, hs, Set.indicator, mul_comm]
    · simp [trapStep, hs, Set.indicator]
  rw [hind, setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le htT, integral_exp_fwd ha]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]

/-- Cochrane (2023), (20.8), p. 474, the forward integral after the trap (`T ≤ t`): `0`. -/
theorem fwd_step_ge {a c T t : ℝ} (htT : T ≤ t) :
    ∫ s in Set.Ioi t, Real.exp (-(a * (s - t))) * trapStep c T s = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun s (hs : t < s) => ?_
  have : ¬ s < T := by linarith
  simp [trapStep, this]

/-- Cochrane (2023), (20.8), p. 475: the constant `C` of the member indexed by `π_T` (the
correspondence `π_T ↦ C` is affine with slope `e^{λ^b T}`):
`C = π_T e^{λ^b T} − (e^{λ^b T} − 1)(λ^f A − κ g)/(λ^f + λ^b)`, `A = −u`. -/
noncomputable def bookC (σ κ ρ T u g πT : ℝ) : ℝ :=
  πT * Real.exp (lamb ρ κ σ * T) -
    (Real.exp (lamb ρ κ σ * T) - 1) * (lamf ρ κ σ * (-u) - κ * g) / (lamf ρ κ σ + lamb ρ κ σ)

/-- Cochrane (2023), (20.8), p. 474 (Stieltjes reading, survey E6): the contribution of the
atoms of `κ dg = κ g(δ_0 − δ_T)` that lie at or before `t`. -/
noncomputable def atomsB (lf lb κ g T t : ℝ) : ℝ :=
  κ * g * (kern lf lb t 0 - if T ≤ t then kern lf lb t T else 0)

/-- Cochrane (2023), (20.8), p. 474 (Stieltjes reading): the contribution of the atom of
`κ dg` that lies after `t` (the `−κ g δ_T` at the end of the trap). -/
noncomputable def atomsF (lf lb κ g T t : ℝ) : ℝ :=
  -(κ * g * if T ≤ t then 0 else kern lf lb t T)

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475: **the book's formulas for the experiment.**
With `dg/dt` read as the measure `g(δ_0 − δ_T)` (survey E6), the member indexed by `π_T` is, for
every `t ≥ 0`, `π_t = C e^{−λ^b t} + (λ^f+λ^b)⁻¹[∫_0^t e^{−λ^b(t−s)}z_s ds +
∫_t^∞ e^{−λ^f(s−t)}z_s ds + atoms]` (20.8) and `κx_t = −κg_t + λ^f C e^{−λ^b t} +
(λ^f+λ^b)⁻¹[λ^f(∫_0^t … + atoms ≤ t) − λ^b(∫_t^∞ … + atoms > t)]` (20.10), with
`C = bookC π_T`. -/
theorem book_form {σ κ ρ T u g : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T) (πT t : ℝ)
    (ht : 0 ≤ t) :
    wPi σ κ ρ T u g πT t = bookC σ κ ρ T u g πT * Real.exp (-(lamb ρ κ σ * t)) +
        ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s) +
          (∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) * zTrap σ κ u T s) +
          atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t + atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) /
          (lamf ρ κ σ + lamb ρ κ σ) ∧
      κ * wX σ κ ρ T u g πT t = -(κ * trapStep g T t) +
        lamf ρ κ σ * bookC σ κ ρ T u g πT * Real.exp (-(lamb ρ κ σ * t)) +
        (lamf ρ κ σ * ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s)
            + atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) -
          lamb ρ κ σ * ((∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) *
            zTrap σ κ u T s) + atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t)) /
          (lamf ρ κ σ + lamb ρ κ σ) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  have hz : ∀ s, zTrap σ κ u T s = trapStep (κ * σ * (0 - u)) T s := fun s => by
    unfold zTrap trapStep; split_ifs <;> ring
  simp only [hz]
  have eA : Real.exp (lamb ρ κ σ * (T - t)) =
      Real.exp (lamb ρ κ σ * T) * Real.exp (-(lamb ρ κ σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  have eB : Real.exp (-(lamb ρ κ σ * (t - T))) =
      Real.exp (lamb ρ κ σ * T) * Real.exp (-(lamb ρ κ σ * t)) := by
    rw [← Real.exp_add]; ring_nf
  rcases le_or_gt t T with htT | htT
  · rw [bwd_step_le hb.ne' ht htT, fwd_step_le hf.ne' htT]
    rcases eq_or_lt_of_le htT with h | h
    · subst h
      simp only [wPi, wX, le_refl, ↓reduceIte, atomsB, atomsF, kern, ht, trapStep, lt_irrefl,
        trapPi, trapY, hh, kk, bookC, sub_self, sub_zero, mul_zero, neg_zero, Real.exp_zero,
        mul_one, Real.exp_neg]
      rw [← hmul]
      constructor
      · field_simp
        ring
      · field_simp
        ring
    · simp only [wPi, wX, htT, ↓reduceIte, atomsB, atomsF, kern, ht, not_le.2 h, trapStep, h,
        trapPi, trapY, hh, kk, bookC, sub_zero]
      rw [eA, ← hmul]
      constructor
      · field_simp
        ring
      · field_simp
        ring
  · rw [bwd_step_ge hb.ne' hT htT.le, fwd_step_ge htT.le]
    simp only [wPi, wX, not_le.2 htT, ↓reduceIte, atomsB, atomsF, kern, ht, htT.le, trapStep,
      not_lt.2 htT.le, bookC, sub_zero]
    rw [eB, ← hmul]
    constructor
    · field_simp
      ring
    · field_simp
      ring

/-- Cochrane (2023), (20.8), p. 474, for the experiment (Stieltjes reading): the right-hand side
of (20.8) with constant `C`. -/
noncomputable def bookPi (σ κ ρ T u g C t : ℝ) : ℝ :=
  C * Real.exp (-(lamb ρ κ σ * t)) +
    ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s) +
      (∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) * zTrap σ κ u T s) +
      atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t + atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) /
      (lamf ρ κ σ + lamb ρ κ σ)

/-- Cochrane (2023), (20.10), p. 475, for the experiment (Stieltjes reading): the right-hand
side of (20.10) (`κ x_t`) with constant `C`. -/
noncomputable def bookKX (σ κ ρ T u g C t : ℝ) : ℝ :=
  -(κ * trapStep g T t) + lamf ρ κ σ * C * Real.exp (-(lamb ρ κ σ * t)) +
    (lamf ρ κ σ * ((∫ s in (0 : ℝ)..t, Real.exp (-(lamb ρ κ σ * (t - s))) * zTrap σ κ u T s) +
        atomsB (lamf ρ κ σ) (lamb ρ κ σ) κ g T t) -
      lamb ρ κ σ * ((∫ s in Set.Ioi t, Real.exp (-(lamf ρ κ σ * (s - t))) * zTrap σ κ u T s) +
        atomsF (lamf ρ κ σ) (lamb ρ κ σ) κ g T t)) / (lamf ρ κ σ + lamb ρ κ σ)

/-- Cochrane (2023), (20.8)–(20.10), pp. 474–475, for the experiment (survey E6): **the bounded
paths are exactly the book's formulas (20.8) and (20.10)**, for some constant `C`, with
`dg/dt` read as the measure `g(δ_0 − δ_T)`. -/
theorem experiment_eq20_8 {σ κ ρ T u g : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T)
    {x π : ℝ → ℝ} :
    (IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
        BddOnIci π) ↔
      ∃ C, ∀ t, 0 ≤ t → π t = bookPi σ κ ρ T u g C t ∧ κ * x t = bookKX σ κ ρ T u g C t := by
  rw [bdd_path_iff hκ hσ]
  constructor
  · rintro ⟨πT, h⟩
    refine ⟨bookC σ κ ρ T u g πT, fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := book_form (ρ := ρ) (u := u) (g := g) hσ hκ hT πT t ht
    rw [(h t ht).1, (h t ht).2]
    exact ⟨h1, h2⟩
  · rintro ⟨C, h⟩
    have hE := Real.exp_pos (lamb ρ κ σ * T)
    set K0 := (Real.exp (lamb ρ κ σ * T) - 1) * (lamf ρ κ σ * (-u) - κ * g) /
      (lamf ρ κ σ + lamb ρ κ σ)
    refine ⟨(C + K0) / Real.exp (lamb ρ κ σ * T), fun t ht => ?_⟩
    have hC : bookC σ κ ρ T u g ((C + K0) / Real.exp (lamb ρ κ σ * T)) = C := by
      simp only [bookC, K0]
      field_simp
      ring
    obtain ⟨h1, h2⟩ := book_form (ρ := ρ) (u := u) (g := g) hσ hκ hT
      ((C + K0) / Real.exp (lamb ρ κ σ * T)) t ht
    rw [hC] at h1 h2
    refine ⟨by rw [(h t ht).1]; exact h1.symm, ?_⟩
    apply mul_left_cancel₀ hκ.ne'
    rw [(h t ht).2]
    exact h2.symm

/-- Cochrane (2023), (20.8), p. 475: the constant `C` in (20.8) is pinned by `π_0`, so it is
unique. -/
theorem bookPi_C_unique {σ κ ρ T u g C C' : ℝ}
    (h : bookPi σ κ ρ T u g C 0 = bookPi σ κ ρ T u g C' 0) : C = C' := by
  simp only [bookPi, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  linarith

/-! ## (20.7): an active rule after `T` selects the chosen path -/

/-- Cochrane (2023), (20.7), p. 474: **deviations from the chosen path under an active rule
explode.** If `p = π − π*` and `d = x − x*` are continuous on `[T, ∞)`, bounded there, and on
`(T, ∞)` (off a countable set) `ḋ = σ(φ − 1)p`, `ṗ = ρp − κd`, with `σ, κ, ρ > 0` and `φ > 1`,
then `p = d = 0` on `[T, ∞)` (both roots of `λ² − ρλ + κσ(φ−1)` have positive real part). -/
theorem active_rule_dev_zero {σ κ ρ φ T : ℝ} {p d : ℝ → ℝ} {S : Set ℝ} (hS : S.Countable)
    (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ) (hφ : 1 < φ) (hpc : ContinuousOn p (Set.Ici T))
    (hdc : ContinuousOn d (Set.Ici T))
    (hd : ∀ t, T < t → t ∉ S →
      HasDerivAt d (σ * (φ - 1) * p t) t ∧ HasDerivAt p (ρ * p t - κ * d t) t)
    (Kp Kd : ℝ) (hpb : ∀ t, T ≤ t → |p t| ≤ Kp) (hdb : ∀ t, T ≤ t → |d t| ≤ Kd) :
    ∀ t, T ≤ t → p t = 0 ∧ d t = 0 := by
  set c := κ * σ * (φ - 1) with hc
  have hcpos : 0 < c := by have := mul_pos hκ hσ; simp only [hc]; nlinarith
  -- `q = ρp − κd` is `ṗ`, and `q̇ = ρq − c p`
  have hqd : ∀ t, T < t → t ∉ S →
      HasDerivAt (fun s => ρ * p s - κ * d s) (ρ * (ρ * p t - κ * d t) - c * p t) t :=
    fun t ht hts => by
      obtain ⟨a, b⟩ := hd t ht hts
      exact ((b.const_mul ρ).sub (a.const_mul κ)).congr_deriv (by simp only [hc]; ring)
  have hqc : ContinuousOn (fun s => ρ * p s - κ * d s) (Set.Ici T) :=
    (continuousOn_const.mul hpc).sub (continuousOn_const.mul hdc)
  have hqb : ∀ t, T ≤ t → |ρ * p t - κ * d t| ≤ ρ * Kp + κ * Kd := fun t ht => by
    calc |ρ * p t - κ * d t| ≤ |ρ * p t| + |κ * d t| := abs_sub _ _
      _ = ρ * |p t| + κ * |d t| := by rw [abs_mul, abs_mul, abs_of_pos hρ, abs_of_pos hκ]
      _ ≤ ρ * Kp + κ * Kd := add_le_add (mul_le_mul_of_nonneg_left (hpb t ht) hρ.le)
          (mul_le_mul_of_nonneg_left (hdb t ht) hκ.le)
  set q : ℝ → ℝ := fun s => ρ * p s - κ * d s with hqdef
  have hpd : ∀ t, T < t → t ∉ S → HasDerivAt p (q t) t := fun t ht hts => (hd t ht hts).2
  have hpq : ∀ t, T ≤ t → p t = 0 ∧ q t = 0 := by
    rcases lt_or_ge (ρ ^ 2) (4 * c) with hdisc | hdisc
    · -- complex roots: `V = q² − ρpq + cp²` grows at rate `ρ`
      have hV := unstable_bdd_zero (f := fun s => q s ^ 2 - ρ * p s * q s + c * p s ^ 2)
        (a := ρ) (p := T) (K := (ρ * Kp + κ * Kd) ^ 2 + ρ * Kp * (ρ * Kp + κ * Kd) + c * Kp ^ 2)
        hρ hS (((hqc.pow 2).sub ((continuousOn_const.mul hpc).mul hqc)).add
          (continuousOn_const.mul (hpc.pow 2)))
        (fun t ht hts => by
          have hq := hqd t ht hts
          have hp := hpd t ht hts
          refine (((hq.pow 2).sub ((hp.const_mul ρ).mul hq)).add
            ((hp.pow 2).const_mul c)).congr_deriv ?_
          simp only [hqdef]
          ring)
        (fun t ht => by
          have h1 := hpb t ht
          have h2 := hqb t ht
          have hKp : 0 ≤ Kp := le_trans (abs_nonneg _) h1
          calc |q t ^ 2 - ρ * p t * q t + c * p t ^ 2|
              ≤ |q t ^ 2| + |ρ * p t * q t| + |c * p t ^ 2| := by
                refine (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
            _ = |q t| ^ 2 + ρ * |p t| * |q t| + c * |p t| ^ 2 := by
                rw [abs_pow, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos hρ,
                  abs_of_pos hcpos]
            _ ≤ (ρ * Kp + κ * Kd) ^ 2 + ρ * Kp * (ρ * Kp + κ * Kd) + c * Kp ^ 2 := by
                have a1 := abs_nonneg (p t)
                have a2 := abs_nonneg (q t)
                gcongr)
      intro t ht
      have h0 := hV t ht
      have e1 : (2 * q t - ρ * p t) ^ 2 + (4 * c - ρ ^ 2) * p t ^ 2 = 0 := by
        linear_combination 4 * h0
      have hp0 : p t = 0 := by
        have := sq_nonneg (2 * q t - ρ * p t)
        have h4 : 0 < 4 * c - ρ ^ 2 := by linarith
        have : (4 * c - ρ ^ 2) * p t ^ 2 = 0 := by nlinarith [sq_nonneg (p t)]
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
      refine ⟨hp0, ?_⟩
      rw [hp0] at e1
      have : (2 * q t) ^ 2 = 0 := by nlinarith
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
      linarith
    · -- real roots `λ₁ ≥ λ₂ > 0`
      set D := Real.sqrt (ρ ^ 2 - 4 * c) with hD
      have hD2 : D ^ 2 = ρ ^ 2 - 4 * c := Real.sq_sqrt (by linarith)
      have hD0 : 0 ≤ D := Real.sqrt_nonneg _
      have hDρ : D < ρ := by
        rw [hD, Real.sqrt_lt' hρ]
        linarith
      set l1 := (ρ + D) / 2
      set l2 := (ρ - D) / 2
      have hl1 : 0 < l1 := by simp only [l1]; linarith
      have hl2 : 0 < l2 := by simp only [l2]; linarith
      have hprod : l1 * l2 = c := by simp only [l1, l2]; linear_combination (-1 / 4) * hD2
      have hsum : l1 + l2 = ρ := by simp only [l1, l2]; ring
      have hm := unstable_bdd_zero (f := fun s => q s - l1 * p s) (a := l2) (p := T)
        (K := (ρ * Kp + κ * Kd) + l1 * Kp) hl2 hS (hqc.sub (continuousOn_const.mul hpc))
        (fun t ht hts => by
          refine ((hqd t ht hts).sub ((hpd t ht hts).const_mul l1)).congr_deriv ?_
          simp only [hqdef]
          linear_combination (p t) * hprod - (ρ * p t - κ * d t) * hsum)
        (fun t ht => by
          calc |q t - l1 * p t| ≤ |q t| + |l1 * p t| := abs_sub _ _
            _ = |q t| + l1 * |p t| := by rw [abs_mul, abs_of_pos hl1]
            _ ≤ (ρ * Kp + κ * Kd) + l1 * Kp :=
              add_le_add (hqb t ht) (mul_le_mul_of_nonneg_left (hpb t ht) hl1.le))
      have hp := unstable_bdd_zero (f := p) (a := l1) (p := T) (K := Kp) hl1 hS hpc
        (fun t ht hts => (hpd t ht hts).congr_deriv (by
          have := hm t ht.le
          linarith)) hpb
      intro t ht
      have h1 := hm t ht
      refine ⟨hp t ht, ?_⟩
      rw [hp t ht] at h1
      linarith
  intro t ht
  obtain ⟨h1, h2⟩ := hpq t ht
  refine ⟨h1, ?_⟩
  simp only [hqdef, h1, mul_zero, zero_sub, neg_eq_zero] at h2
  rcases mul_eq_zero.1 h2 with h | h
  · linarith
  · exact h

/-- Cochrane (2023), (20.7), p. 474: **adding active monetary policy after the trap selects the
chosen path.** Let `(x*, π*)` solve (20.5)–(20.6) on `(T, ∞)` with interest rate `i*`, and
`(x, π)` solve them with the rule `i = i* + φ(π − π*)`, `φ > 1` (same `u_r`, `g`). If both are
continuous and bounded on `[T, ∞)` then `(x, π) = (x*, π*)` on `[T, ∞)`. -/
theorem eq20_7_selects {σ κ ρ φ T : ℝ} {istar u g x π xs πs : ℝ → ℝ} {S : Set ℝ}
    (hS : S.Countable) (hσ : 0 < σ) (hκ : 0 < κ) (hρ : 0 < ρ) (hφ : 1 < φ)
    (hxc : ContinuousOn x (Set.Ici T)) (hπc : ContinuousOn π (Set.Ici T))
    (hxsc : ContinuousOn xs (Set.Ici T)) (hπsc : ContinuousOn πs (Set.Ici T))
    (h : ∀ t, T < t → t ∉ S →
      HasDerivAt x (σ * ((istar t + φ * (π t - πs t)) - π t - u t)) t ∧
        HasDerivAt π (ρ * π t - κ * (x t + g t)) t)
    (hs : ∀ t, T < t → t ∉ S →
      HasDerivAt xs (σ * (istar t - πs t - u t)) t ∧
        HasDerivAt πs (ρ * πs t - κ * (xs t + g t)) t)
    (Kx Kπ Kxs Kπs : ℝ) (hxb : ∀ t, T ≤ t → |x t| ≤ Kx) (hπb : ∀ t, T ≤ t → |π t| ≤ Kπ)
    (hxsb : ∀ t, T ≤ t → |xs t| ≤ Kxs) (hπsb : ∀ t, T ≤ t → |πs t| ≤ Kπs) :
    ∀ t, T ≤ t → π t = πs t ∧ x t = xs t := by
  have := active_rule_dev_zero (p := fun s => π s - πs s) (d := fun s => x s - xs s) hS hσ hκ
    hρ hφ (hπc.sub hπsc) (hxc.sub hxsc)
    (fun t ht hts => by
      obtain ⟨a, b⟩ := h t ht hts
      obtain ⟨a', b'⟩ := hs t ht hts
      exact ⟨(a.sub a').congr_deriv (by ring), (b.sub b').congr_deriv (by ring)⟩)
    (Kπ + Kπs) (Kx + Kxs)
    (fun t ht => (abs_sub _ _).trans (add_le_add (hπb t ht) (hπsb t ht)))
    (fun t ht => (abs_sub _ _).trans (add_le_add (hxb t ht) (hxsb t ht)))
  intro t ht
  obtain ⟨h1, h2⟩ := this t ht
  exact ⟨by linarith, by linarith⟩

end Cochrane.ZeroBound.WerningModel
