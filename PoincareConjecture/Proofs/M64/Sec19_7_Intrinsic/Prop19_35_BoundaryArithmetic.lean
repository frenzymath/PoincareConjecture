import PoincareConjecture.Statements.M64Comparison

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture

theorem m64Intrinsic_boundarySpeed_nonneg (N : IntrinsicAnnulus)
    (radius x : ℝ) :
    0 ≤ intrinsicBoundarySpeed N.metric radius x := by
  exact Real.sqrt_nonneg _

theorem m64Intrinsic_boundaryLength_nonneg (N : IntrinsicAnnulus)
    (radius a b : ℝ) (hab : a ≤ b) :
    0 ≤ intrinsicBoundaryLength N.metric radius a b := by
  unfold intrinsicBoundaryLength
  exact intervalIntegral.integral_nonneg hab
    (fun _ _ => m64Intrinsic_boundarySpeed_nonneg N radius _)

theorem m64Intrinsic_geodesicCurvatureIntegral_nonneg (N : IntrinsicAnnulus)
    (radius a b : ℝ) (hab : a ≤ b) :
    0 ≤ intrinsicGeodesicCurvatureIntegral N.metric N.connection radius a b := by
  unfold intrinsicGeodesicCurvatureIntegral
  apply intervalIntegral.integral_nonneg hab
  intro x _
  exact mul_nonneg (Real.sqrt_nonneg _) (m64Intrinsic_boundarySpeed_nonneg N radius x)

end PoincareConjecture
