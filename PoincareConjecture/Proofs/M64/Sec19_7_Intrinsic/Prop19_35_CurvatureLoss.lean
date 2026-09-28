import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TotalTurning















noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture



def m64IntrinsicHighCurvatureLength (N : IntrinsicAnnulus) (alpha : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) rampPeriod ∩
    {x | alpha < intrinsicGeodesicCurvature N.metric N.connection 1 x},
    intrinsicBoundarySpeed N.metric 1 x




theorem m64Intrinsic_continuous_geodesicCurvature
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0) :
    Continuous (fun x => intrinsicGeodesicCurvature N.metric N.connection radius x) := by
  have h := (m64Intrinsic_continuous_turning_density N hradius).div
    (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous
    (fun x => (m64Intrinsic_boundarySpeed_pos N hradius x).ne')
  convert h using 1
  funext x
  exact (mul_div_cancel_right₀ _ (m64Intrinsic_boundarySpeed_pos N hradius x).ne').symm



theorem m64IntrinsicHighCurvatureLength_nonneg (N : IntrinsicAnnulus) (alpha : ℝ) :
    0 ≤ m64IntrinsicHighCurvatureLength N alpha := by
  exact integral_nonneg (fun _ => Real.sqrt_nonneg _)




theorem m64Intrinsic_high_curvature_length_mul_le_turning
    (N : IntrinsicAnnulus) (alpha : ℝ) :
    alpha * m64IntrinsicHighCurvatureLength N alpha ≤
      intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod := by
  let speed := intrinsicBoundarySpeed N.metric 1
  let density := fun x => intrinsicGeodesicCurvature N.metric N.connection 1 x * speed x
  let Y := Ioc (0 : ℝ) rampPeriod ∩
    {x | alpha < intrinsicGeodesicCurvature N.metric N.connection 1 x}
  have hspeed := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hdensity := m64Intrinsic_continuous_turning_density N (by norm_num : (1 : ℝ) ≠ 0)
  have hspeedI : IntegrableOn speed (Ioc (0 : ℝ) rampPeriod) :=
    hspeed.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hdensityI : IntegrableOn density (Ioc (0 : ℝ) rampPeriod) :=
    hdensity.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hY : MeasurableSet Y := measurableSet_Ioc.inter
    (isOpen_lt continuous_const
      (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0))).measurableSet
  have hpoint : (∫ x in Y, alpha * speed x) ≤ ∫ x in Y, density x := by
    apply setIntegral_mono_on
      ((hspeedI.mono_set inter_subset_left).const_mul alpha)
      (hdensityI.mono_set inter_subset_left) hY
    intro x hx
    exact mul_le_mul_of_nonneg_right hx.2.le (Real.sqrt_nonneg _)
  have htotal : (∫ x in Y, density x) ≤
      ∫ x in Ioc (0 : ℝ) rampPeriod, density x := by
    apply setIntegral_mono_set hdensityI
    · exact Filter.Eventually.of_forall (fun x => mul_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))
    · exact Filter.Eventually.of_forall (fun _ hx => hx.1)
  rw [integral_const_mul] at hpoint
  change alpha * m64IntrinsicHighCurvatureLength N alpha ≤ _ at hpoint
  apply hpoint.trans
  rw [intrinsicGeodesicCurvatureIntegral,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ rampPeriod from Real.two_pi_pos.le)]
  exact htotal




theorem m64Intrinsic_high_curvature_length_lt
    (N : IntrinsicAnnulus) {delta r alpha : ℝ} (hdelta : 0 < delta) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / r ≤ alpha) :
    m64IntrinsicHighCurvatureLength N alpha <
      intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 := by
  have hturning := m64Intrinsic_total_turning_lt N hdelta hr hfirst hturn
  have hscale := mul_le_mul_of_nonneg_right halpha
    (m64IntrinsicHighCurvatureLength_nonneg N alpha)
  have hless := (hscale.trans (m64Intrinsic_high_curvature_length_mul_le_turning N alpha)).trans_lt
    hturning
  have hfactor : 0 < 100 * delta / r := by positivity
  have heq : (2 * delta / r) * intrinsicBoundaryLength N.metric 1 0 rampPeriod =
      (100 * delta / r) * (intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50) := by ring
  rw [heq] at hless
  exact (mul_lt_mul_iff_right₀ hfactor).mp hless

end PoincareConjecture
