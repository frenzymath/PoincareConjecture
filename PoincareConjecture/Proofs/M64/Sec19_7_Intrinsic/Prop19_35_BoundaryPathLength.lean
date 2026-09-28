import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionMinimizer
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Energy.Length




noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ENNReal Manifold ContDiff

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_boundary_pathELength
    (N : IntrinsicAnnulus) {radius a b : ℝ} (hradius : radius ≠ 0) (hab : a ≤ b) :
    N.metric.pathELength (intrinsicAnnulusBoundary radius) a b =
      ENNReal.ofReal (intrinsicBoundaryLength N.metric radius a b) := by
  exact N.metric.pathELength_eq_ofReal_integral_speed hab
    (m64Intrinsic_contDiff_boundarySpeed N hradius).continuous.continuousOn




theorem m64Intrinsic_boundary_curveVariation_le
    (N : IntrinsicAnnulus) {radius a b : ℝ} (hradius : radius ≠ 0) (hab : a ≤ b) :
    m64IntrinsicCurveVariation N.metric (intrinsicAnnulusBoundary radius) a b ≤
      ENNReal.ofReal (intrinsicBoundaryLength N.metric radius a b) := by
  rw [← m64Intrinsic_boundary_pathELength N hradius hab]
  exact m64Intrinsic_curveVariation_le_pathELength N.metric
    ((contMDiff_iff_contDiff.mpr
      (m64Intrinsic_contDiff_boundary radius)).of_le (by simp)).contMDiffOn




theorem m64Intrinsic_unit_curveVariation_le
    (N : IntrinsicAnnulus) {γ : ℝ → AnnulusCoordinates} {a b : ℝ}
    (hγ : ContDiff ℝ ∞ γ)
    (hunit : ∀ t ∈ Icc a b, N.metric.inner (γ t) (deriv γ t) (deriv γ t) = 1) :
    m64IntrinsicCurveVariation N.metric γ a b ≤ ENNReal.ofReal (b - a) := by
  have hlength : N.metric.pathELength γ a b = ENNReal.ofReal (b - a) := by
    have h := N.metric.pathELength_eq_of_tangentNorm_eq (C := 1) (by
      intro t ht
      change Real.sqrt (N.metric.inner (γ t) (curveVelocity (n := 2) γ t)
        (curveVelocity (n := 2) γ t)) = 1
      rw [m64Intrinsic_curveVelocity_eq_deriv]
      exact (congrArg Real.sqrt (hunit t ht)).trans Real.sqrt_one)
    simpa only [ENNReal.ofReal_one, one_mul] using h
  rw [← hlength]
  exact m64Intrinsic_curveVariation_le_pathELength N.metric
    ((contMDiff_iff_contDiff.mpr hγ).of_le (by simp)).contMDiffOn

end PoincareConjecture
