import PoincareLib.Geometry.CurveShortening.Comparison.Theory

/-!
# Proposition 19.35: boundary-length bookkeeping

The intrinsic boundary speed is a metric tangent norm, hence nonnegative.
These interval-integral lemmas are the small analytic facts used when the
absolute-turning hypotheses are split into subarcs.

Context: Morgan--Tian Proposition 19.35, printed pp. 467-481; actual intrinsic
boundary, scalar comparison or endpoint assembly.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareMT

/-- The exact intrinsic circle speed is nonnegative. Source: MT Proposition 19.35, pp.
467-481; `reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_boundarySpeed_nonneg (N : IntrinsicAnnulus)
    (radius x : ℝ) :
    0 ≤ intrinsicBoundarySpeed N.metric radius x := by
  exact Real.sqrt_nonneg _

/-- The intrinsic boundary length is nonnegative on an ordered parameter interval. Source:
MT Proposition 19.35, pp. 467-481; `reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_boundaryLength_nonneg (N : IntrinsicAnnulus)
    (radius a b : ℝ) (hab : a ≤ b) :
    0 ≤ intrinsicBoundaryLength N.metric radius a b := by
  unfold intrinsicBoundaryLength
  exact intervalIntegral.integral_nonneg hab
    (fun _ _ => m64Intrinsic_boundarySpeed_nonneg N radius _)

/-- The exact absolute geodesic-curvature integral is nonnegative on an ordered interval.
Source: MT Proposition 19.35, pp. 467-481; `reports/2026-09-23-intrinsic-assembly.md`. -/
theorem m64Intrinsic_geodesicCurvatureIntegral_nonneg (N : IntrinsicAnnulus)
    (radius a b : ℝ) (hab : a ≤ b) :
    0 ≤ intrinsicGeodesicCurvatureIntegral N.metric N.connection radius a b := by
  unfold intrinsicGeodesicCurvatureIntegral
  apply intervalIntegral.integral_nonneg hab
  intro x _
  exact mul_nonneg (Real.sqrt_nonneg _) (m64Intrinsic_boundarySpeed_nonneg N radius x)

end PoincareMT
