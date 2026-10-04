import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! A change of circle origin preserves integrability and actual integrals.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareMT

/-- A full-period phase shift preserves actual integrability of a periodic field. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Periodic_integrableOn_shift
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hperiod : Function.Periodic f T) (hf : IntegrableOn f (Icc (0 : ℝ) T) volume)
    (a : ℝ) : IntegrableOn (fun x => f (x + a)) (Icc (0 : ℝ) T) volume := by
  have hi : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hf
  have ha := (hperiod.intervalIntegrable₀ hT.ne' hi a (a + T)).comp_add_right a
  have ha' : IntervalIntegrable (fun x => f (x + a)) volume 0 T := by
    simpa only [sub_self, add_sub_cancel_left] using ha
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp ha'

/-- A full-period phase shift preserves actual L2 integrability of a periodic field. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Periodic_memLp_two_shift
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hperiod : Function.Periodic f T) (hf : MemLp f 2 (volume.restrict (Icc (0 : ℝ) T)))
    (a : ℝ) : MemLp (fun x => f (x + a)) 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  have hi := m64Periodic_integrableOn_shift hT hperiod (hf.integrable (by norm_num)) a
  have hs : Function.Periodic (fun x => ‖f x‖ ^ 2) T :=
    fun x => congrArg (fun z : E => ‖z‖ ^ 2) (hperiod x)
  have hsq := m64Periodic_integrableOn_shift hT hs
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf) a
  exact (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr hsq

/-- A phase shift preserves the actual integral over one full period. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Periodic_integral_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {T : ℝ} (hT : 0 < T) (hperiod : Function.Periodic f T) (a : ℝ) :
    (∫ x in Icc (0 : ℝ) T, f (x + a)) = ∫ x in Icc (0 : ℝ) T, f x := by
  have hshift := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := T) f a
  have hperiodInt := hperiod.intervalIntegral_add_eq a 0
  rw [zero_add, add_comm T a] at hshift
  rw [zero_add] at hperiodInt
  have h := hshift.trans hperiodInt
  simpa only [intervalIntegral.integral_of_le hT.le,
    ← integral_Icc_eq_integral_Ioc] using h

/-- The ordinary derivative of a periodic function is periodic. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64Periodic_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {T : ℝ} (hperiod : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  have heq : (fun x => f (x + T)) = f := funext hperiod
  intro x
  rw [← deriv_comp_add_const, heq]

end PoincareMT
