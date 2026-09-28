import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityAveragingWeak
import PoincareConjecture.Proofs.M65.Mathlib.WeightedCauchySchwarz

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M65Interior

theorem averagingProfile_bounded : ∃ B : ℝ, 0 < B ∧ ∀ z, averagingProfile z ≤ B := by
  have hc : Continuous averagingProfile :=
    EuclideanMollificationNative.mollifier_continuous (by norm_num : (0 : ℝ) < 1)
  obtain ⟨z0, hz0⟩ := hc.exists_forall_ge_of_hasCompactSupport
    (EuclideanMollificationNative.mollifier_compactSupport
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨1 + |averagingProfile z0|, by positivity, fun z => ?_⟩
  exact (hz0 z).trans (by linarith [le_abs_self (averagingProfile z0)])

theorem averagingValue_sq_le {B : ℝ} (hB : ∀ z, averagingProfile z ≤ B)
    {r : ℝ} (hr : 0 < r) (x : LoopPlane) {f : LoopPlane → ℝ}
    (hf : MemLp f 2 (volume.restrict (closedBall x r))) :
    averagingValue f r x ^ 2 ≤ B * r⁻¹ ^ 2 * ∫ z in closedBall x r, f z ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (closedBall x r)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall x r).measure_lt_top⟩
  let w : LoopPlane → ℝ := fun z => averagingKernel r (x - z)
  have hc : Continuous w := (averagingKernel_contDiff r).continuous.comp (by fun_prop)
  have hz (z : LoopPlane) (h : z ∉ closedBall x r) : w z = 0 := by
    by_contra hne
    apply h
    rw [mem_closedBall_iff_norm']
    exact mem_closedBall_zero_iff.mp (averagingKernel_support hr hne)
  have hw : IntegrableOn w (closedBall x r) :=
    hc.continuousOn.integrableOn_compact (isCompact_closedBall x r)
  have hf1 : IntegrableOn f (closedBall x r) := hf.integrable (by norm_num)
  have hf2 : IntegrableOn (fun z => f z ^ 2) (closedBall x r) := hf.integrable_sq
  have hfw : IntegrableOn (fun z => f z * w z) (closedBall x r) :=
    hf1.mul_continuousOn hc.continuousOn (isCompact_closedBall x r)
  have hf2w : IntegrableOn (fun z => f z ^ 2 * w z) (closedBall x r) :=
    hf2.mul_continuousOn hc.continuousOn (isCompact_closedBall x r)
  have hmass : (∫ z in closedBall x r, w z) = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    change (∫ z, averagingKernel r (x - z)) = 1
    rw [integral_sub_left_eq_self, averagingKernel_integral hr]
  have hav : averagingValue f r x = ∫ z in closedBall x r, f z * w z := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z h => by rw [hz z h, mul_zero])
  have hcs := integral_mul_weight_sq_le
    (mu := volume.restrict (closedBall x r))
    (ae_of_all _ (fun z => averagingKernel_nonneg r (x - z))) hw hfw hf2w
  rw [hmass, one_mul] at hcs
  have hbound : (∫ z in closedBall x r, f z ^ 2 * w z) ≤
      B * r⁻¹ ^ 2 * ∫ z in closedBall x r, f z ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae hf2w (hf.integrable_sq.const_mul _)
    filter_upwards with z
    have hwz : w z ≤ B * r⁻¹ ^ 2 := by
      change r⁻¹ ^ 2 * averagingProfile (r⁻¹ • (x - z)) ≤ _
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hB (r⁻¹ • (x - z))) (sq_nonneg r⁻¹)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hwz (sq_nonneg (f z))
  rw [hav]
  exact hcs.trans hbound

end PoincareConjecture.M65Interior
