import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FormIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem absoluteContinuous_of_dist_le {f : ℝ → E} {g : ℝ → F} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)))
    ?_ hg
  rw [eventually_inf_principal]
  filter_upwards with z hz
  exact Finset.sum_le_sum (fun i hi => hfg _ (hz.1 i hi).1 _ (hz.1 i hi).2)

theorem absoluteContinuous_bochner_primitive [CompleteSpace E]
    {f : ℝ → E} {a b c : ℝ} (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in c..t, f s) a b := by
  apply absoluteContinuous_of_dist_le
    (hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc)
  intro x hx y hy
  have hcx : IntervalIntegrable f volume c x := hf.mono_set (uIcc_subset_uIcc hc hx)
  have hcy : IntervalIntegrable f volume c y := hf.mono_set (uIcc_subset_uIcc hc hy)
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left hcx hcy,
    intervalIntegral.integral_interval_sub_left hcx.norm hcy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

theorem absoluteContinuous_clm_apply {A : ℝ → E →L[ℝ] F} {u : ℝ → E} {a b : ℝ}
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hu : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun t => A t (u t)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hu.exists_bound
  unfold AbsolutelyContinuousOnInterval at hA hu ⊢
  apply squeeze_zero' (Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => dist_nonneg)))
    ?_ (by simpa using (hu.const_mul C).add (hA.const_mul D))
  rw [eventually_inf_principal]
  filter_upwards with z hz
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hx := (hz.1 i hi).1
  have hy := (hz.1 i hi).2
  calc
    dist (A (z.2 i).1 (u (z.2 i).1)) (A (z.2 i).2 (u (z.2 i).2)) ≤
        dist (A (z.2 i).1 (u (z.2 i).1)) (A (z.2 i).1 (u (z.2 i).2)) +
          dist (A (z.2 i).1 (u (z.2 i).2)) (A (z.2 i).2 (u (z.2 i).2)) :=
      dist_triangle _ _ _
    _ ≤ C * dist (u (z.2 i).1) (u (z.2 i).2) +
        D * dist (A (z.2 i).1) (A (z.2 i).2) := by
      simp only [dist_eq_norm, ← map_sub, ← sub_apply]
      apply add_le_add
      · exact ((A (z.2 i).1).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hC _ hx) (norm_nonneg _))
      · exact ((A (z.2 i).1 - A (z.2 i).2).le_opNorm _).trans
          ((mul_le_mul_of_nonneg_left (hD _ hy) (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem absoluteContinuous_integral_eq [CompleteSpace E] {f f' : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfi : IntervalIntegrable f' volume a b)
    (hfd : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt f (f' t) t) :
    ∀ t ∈ uIcc a b, f t = f a + ∫ s in a..t, f' s := by
  have hp := absoluteContinuous_bochner_primitive hfi (left_mem_uIcc : a ∈ uIcc a b)
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun r => f r - ∫ s in a..r, f' s) 0 t := by
    filter_upwards [hfd, hfi.ae_hasDerivAt_integral] with t ht hp htmem
    simpa only [Pi.sub_apply, sub_self] using! (ht htmem).sub (hp htmem a left_mem_uIcc)
  obtain ⟨C, hC⟩ := (hf.fun_sub hp).const_of_ae_hasDerivAt_zero hd
  have hCa : f a = C := by
    simpa only [intervalIntegral.integral_same, sub_zero] using hC a left_mem_uIcc
  intro t ht
  have he := hC t ht
  rw [← hCa] at he
  exact sub_eq_iff_eq_add.mp he

end PoincareConjecture.M35.Uniqueness.Heat
