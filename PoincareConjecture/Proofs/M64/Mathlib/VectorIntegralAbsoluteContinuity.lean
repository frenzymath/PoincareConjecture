import Mathlib.MeasureTheory.Function.AbsolutelyContinuous











set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture






theorem intervalIntegral_vector_absolutelyContinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b c : ℝ} (hf : IntervalIntegrable f volume a b)
    (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, f t) a b := by
  have hnorm : AbsolutelyContinuousOnInterval
      (fun x => ∫ t in c..x, ‖f t‖) a b :=
    hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  rw [absolutelyContinuousOnInterval_iff] at hnorm ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hnorm ε hε
  refine ⟨δ, hδ, fun I hI hlen => ?_⟩
  refine lt_of_le_of_lt (Finset.sum_le_sum fun i hi => ?_) (hbound I hI hlen)
  have hcu : IntervalIntegrable f volume c (I.2 i).1 :=
    hf.mono_set (uIcc_subset_uIcc hc (hI.1 i hi).1)
  have hcv : IntervalIntegrable f volume c (I.2 i).2 :=
    hf.mono_set (uIcc_subset_uIcc hc (hI.1 i hi).2)
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left hcu hcv,
    intervalIntegral.integral_interval_sub_left hcu.norm hcv.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

end PoincareConjecture
