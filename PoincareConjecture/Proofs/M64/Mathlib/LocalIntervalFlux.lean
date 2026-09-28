import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic













noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace PoincareConjecture




theorem m64Interval_local_flux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {P x r : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x - r) (hP : x + r ≤ P)
    (hf : IntegrableOn f (Icc (0 : ℝ) P)) (hg : IntegrableOn g (Icc (0 : ℝ) P))
    (heq : EqOn f g (Icc 0 P \ Icc (x - r) (x + r))) :
    (∫ y in Icc (0 : ℝ) P, f y) - (∫ y in Icc (0 : ℝ) P, g y) =
      (∫ s in (-r)..r, f (s + x)) - ∫ s in (-r)..r, g (s + x) := by
  have hsub : Icc (x - r) (x + r) ⊆ Icc (0 : ℝ) P := Icc_subset_Icc hx hP
  have hab : x - r ≤ x + r := by linarith
  have hfi : IntervalIntegrable f volume (x - r) (x + r) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hf.mono_set hsub)
  have hgi : IntervalIntegrable g volume (x - r) (x + r) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hg.mono_set hsub)
  calc
    _ = ∫ y in Icc (0 : ℝ) P, f y - g y := (integral_sub hf hg).symm
    _ = ∫ y in Icc (x - r) (x + r), f y - g y :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub
        (fun y hy => sub_eq_zero.mpr (heq hy))
    _ = ∫ y in (x - r)..(x + r), f y - g y := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    _ = (∫ y in (x - r)..(x + r), f y) - ∫ y in (x - r)..(x + r), g y :=
      intervalIntegral.integral_sub hfi hgi
    _ = _ := by
      rw [intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_add_right]
      congr 2 <;> ring

end PoincareConjecture
