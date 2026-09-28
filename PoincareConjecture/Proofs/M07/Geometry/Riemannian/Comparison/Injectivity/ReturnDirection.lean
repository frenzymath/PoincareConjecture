import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

private theorem eventually_lt_of_negative_derivative
    {f : ℝ → ℝ} {a : ℝ} (hf : HasDerivAt f a 0) (ha : a < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have hs := (hf.hasDerivWithinAt (s := Ioi 0)).limsup_slope_le' (by simp) ha
  filter_upwards [hs, self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field, sub_zero, div_lt_iff₀ htpos, zero_mul] at ht
  exact sub_neg.mp ht



theorem not_both_derivatives_neg_at_min_max
    {f g : ℝ → ℝ} {a b : ℝ} (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hmin : IsLocalMin (fun t => max (f t) (g t)) 0) : ¬ (a < 0 ∧ b < 0) := by
  intro hneg
  have hfl := eventually_lt_of_negative_derivative hf hneg.1
  have hgl := eventually_lt_of_negative_derivative hg hneg.2
  have hm : ∀ᶠ t in 𝓝[>] (0 : ℝ), max (f 0) (g 0) ≤ max (f t) (g t) :=
    hmin.filter_mono nhdsWithin_le_nhds
  have hfalse : ∀ᶠ t in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hfl, hgl, hm] with t hft hgt hmt
    exact (not_lt_of_ge hmt) (max_lt
      (hft.trans_le (le_max_left _ _)) (hgt.trans_le (le_max_right _ _)))
  exact hfalse.exists.choose_spec



theorem gradients_eq_neg_of_min_max
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {f g : F → ℝ} {x u v : F}
    (hf : HasFDerivAt f (innerSL ℝ u) x)
    (hg : HasFDerivAt g (innerSL ℝ v) x)
    (hnorm : ‖u‖ = ‖v‖)
    (hmin : IsLocalMin (fun y => max (f y) (g y)) x) : u = -v := by
  by_contra hne
  have huv : u + v ≠ 0 := by
    intro h
    exact hne (eq_neg_of_add_eq_zero_left h)
  have hsq : 0 < ‖u + v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr huv)
  rw [norm_add_sq_real, hnorm] at hsq
  have hu : inner ℝ u (-(u + v)) < 0 := by
    rw [inner_neg_right, inner_add_right, real_inner_self_eq_norm_sq, hnorm]
    linarith
  have hv : inner ℝ v (-(u + v)) < 0 := by
    rw [inner_neg_right, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm u v]
    linarith
  let c : ℝ → F := fun t => x + t • (-(u + v))
  have hc : HasDerivAt c (-(u + v)) 0 := by
    simpa [c] using ((hasDerivAt_id (0 : ℝ)).smul_const (-(u + v))).const_add x
  have hc0 : c 0 = x := by simp [c]
  have hf' : HasDerivAt (fun t => f (c t)) (inner ℝ u (-(u + v))) 0 := by
    simpa only [Function.comp_def, innerSL_apply_apply] using
      (hc0.symm ▸ hf).comp_hasDerivAt 0 hc
  have hg' : HasDerivAt (fun t => g (c t)) (inner ℝ v (-(u + v))) 0 := by
    simpa only [Function.comp_def, innerSL_apply_apply] using
      (hc0.symm ▸ hg).comp_hasDerivAt 0 hc
  have hm : IsLocalMin (fun t => max (f (c t)) (g (c t))) 0 := by
    have ht : Tendsto c (𝓝 0) (𝓝 x) := hc0 ▸ hc.continuousAt
    change ∀ᶠ t in 𝓝 0, max (f (c 0)) (g (c 0)) ≤ max (f (c t)) (g (c t))
    rw [hc0]
    exact ht hmin
  exact not_both_derivatives_neg_at_min_max hf' hg' hm ⟨hu, hv⟩



theorem eq_neg_of_min_max_bilinear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBpos : ∀ u, u ≠ 0 → 0 < B u u)
    {f g : F → ℝ} {x u v : F}
    (hf : HasFDerivAt f (B u) x) (hg : HasFDerivAt g (B v) x)
    (hnorm : B u u = B v v)
    (hmin : IsLocalMin (fun y => max (f y) (g y)) x) : u = -v := by
  by_contra hne
  have huv : u + v ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
  have hpos := hBpos (u + v) huv
  simp only [map_add, add_apply] at hpos
  rw [hBsymm v u, hnorm] at hpos
  have hu : B u (-(u + v)) < 0 := by
    rw [map_neg, map_add, hnorm]
    linarith
  have hv : B v (-(u + v)) < 0 := by
    rw [map_neg, map_add, hBsymm v u]
    linarith
  let c : ℝ → F := fun t => x + t • (-(u + v))
  have hc : HasDerivAt c (-(u + v)) 0 := by
    simpa [c] using ((hasDerivAt_id (0 : ℝ)).smul_const (-(u + v))).const_add x
  have hc0 : c 0 = x := by simp [c]
  have hf' : HasDerivAt (fun t => f (c t)) (B u (-(u + v))) 0 := by
    simpa only [Function.comp_def] using (hc0.symm ▸ hf).comp_hasDerivAt 0 hc
  have hg' : HasDerivAt (fun t => g (c t)) (B v (-(u + v))) 0 := by
    simpa only [Function.comp_def] using (hc0.symm ▸ hg).comp_hasDerivAt 0 hc
  have hm : IsLocalMin (fun t => max (f (c t)) (g (c t))) 0 := by
    have ht : Tendsto c (𝓝 0) (𝓝 x) := hc0 ▸ hc.continuousAt
    change ∀ᶠ t in 𝓝 0, max (f (c 0)) (g (c 0)) ≤ max (f (c t)) (g (c t))
    rw [hc0]
    exact ht hmin
  exact not_both_derivatives_neg_at_min_max hf' hg' hm ⟨hu, hv⟩

end PoincareConjecture
