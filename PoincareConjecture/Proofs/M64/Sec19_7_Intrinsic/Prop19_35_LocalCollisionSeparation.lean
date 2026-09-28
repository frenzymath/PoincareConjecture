import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingLoss
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SubarcLengthDecrease
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryPeriodicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral

namespace PoincareConjecture

theorem m64Intrinsic_complementary_boundary_length (N : IntrinsicAnnulus) (a b : ℝ) :
    intrinsicBoundaryLength N.metric 1 a b +
      intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) =
        intrinsicBoundaryLength N.metric 1 0 rampPeriod := by
  have hs := (m64Intrinsic_contDiff_boundarySpeed N one_ne_zero).continuous
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hs.intervalIntegrable a b) (hs.intervalIntegrable b (a + rampPeriod))
  have hperiod := (m64Intrinsic_boundarySpeed_periodic N 1).intervalIntegral_add_eq a 0
  simpa only [intrinsicBoundaryLength, zero_add] using hadd.trans hperiod

theorem m64Intrinsic_no_focusing_of_curvature_bound
    (N : IntrinsicAnnulus) {a b rho kappa M : ℝ}
    (hab : a < b) (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hangle : kappa * rho ≤ Real.pi / 4) (hsmall : 2 * rho * M < 1)
    (hcurv : ∀ p ∈ Icc a b, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ M)
    (hfocus : Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
      (Real.sin (kappa * rho) / kappa) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) : False := by
  have hlen := m64Intrinsic_boundaryLength_pos N one_ne_zero hab
  have hs := (m64Intrinsic_contDiff_boundarySpeed N one_ne_zero).continuous
  have ht := m64Intrinsic_continuous_turning_density N one_ne_zero
  have hturn : intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b ≤
      M * intrinsicBoundaryLength N.metric 1 a b := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hab.le (ht.intervalIntegrable a b)
      ((continuous_const.mul hs).intervalIntegrable a b)
      (fun p hp => mul_le_mul_of_nonneg_right (hcurv p hp)
        (m64Intrinsic_boundarySpeed_nonneg N 1 p))
    simpa only [intrinsicGeodesicCurvatureIntegral, intrinsicBoundaryLength,
      Pi.mul_apply, intervalIntegral.integral_const_mul] using h
  have hbound := m64Intrinsic_sine_focusing_length_le_twice_radius_turning hrho hkappa
    hangle hlen.le (m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 a b hab.le) hfocus
  have hupper := mul_le_mul_of_nonneg_left hturn (by positivity : 0 ≤ 2 * rho)
  have hstrict := mul_lt_mul_of_pos_right hsmall hlen
  nlinarith only [hbound, hupper, hstrict]

theorem m64Intrinsic_no_local_cyclic_focusing
    (N : IntrinsicAnnulus) {a b q rho kappa M : ℝ}
    (hab : a < b) (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hangle : kappa * rho ≤ Real.pi / 4) (hsmall : 2 * rho * M < 1)
    (hcurv : ∀ p ∈ Icc a b, intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ M)
    (hgap : intrinsicBoundaryLength N.metric 1 a b <
      intrinsicBoundaryLength N.metric 1 0 rampPeriod - 2 * q)
    (hfocus :
      (intrinsicBoundaryLength N.metric 1 a b ≤ 2 * q ∧
        Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) ∨
      (intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤ 2 * q ∧
        Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤
          (Real.sin (kappa * rho) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 b (a + rampPeriod))) :
    False := by
  rcases hfocus with hfocus | hfocus
  · exact m64Intrinsic_no_focusing_of_curvature_bound N hab hrho hkappa hangle hsmall
      hcurv hfocus.2
  · have hsum := m64Intrinsic_complementary_boundary_length N a b
    linarith only [hgap, hsum, hfocus.1]

end PoincareConjecture
