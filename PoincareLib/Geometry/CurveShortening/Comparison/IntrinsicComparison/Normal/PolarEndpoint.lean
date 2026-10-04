import PoincareLib.Geometry.CurveShortening.Comparison.Analysis.Radial.ArcDerivative
import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Varying.FocusingArc

/-! The original normal side supplies the radial field's endpoint pairing.
Source: MT Remark 19.42; short-geodesic-digons derivation, Section 12. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- Equality with the original reversed normal side forces every pushed scalar radial field
to be orthogonal to the actual boundary unit tangent. Source: MT Remark 19.42; digon
derivation, Section 12. Source/construction:
proof-work/tasks/M64/derivations/2026-09-27-short-geodesic-digons.md, Section 12. -/
theorem m64Intrinsic_normal_polar_endpoint_orthogonal
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    {v : AnnulusCoordinates} (he : DifferentiableAt ℝ e v)
    {gamma : ℝ → AnnulusCoordinates} (hg : DifferentiableAt ℝ gamma 0) {T a : ℝ}
    (hvalue : ∀ t ∈ Icc (0 : ℝ) 1, e (t • v) = gamma (T - T * t))
    (horth : N.metric.inner (intrinsicAnnulusBoundary 1 a)
      (deriv (intrinsicAnnulusBoundary 1) a) (deriv gamma 0) = 0) (c : ℝ) :
    N.metric.inner (intrinsicAnnulusBoundary 1 a) (fderiv ℝ e v (c • v))
      (intrinsicBoundaryUnitTangent N.metric 1 a) = 0 := by
  have hd := m64_radial_terminal_derivative_of_closed_reverse he hg hvalue
  have ho : N.metric.inner (intrinsicAnnulusBoundary 1 a) (deriv gamma 0)
      (deriv (intrinsicAnnulusBoundary 1) a) = 0 := by
    rw [N.metric.symm]
    exact horth
  simp only [map_smul, hd, intrinsicBoundaryUnitTangent,
    m64Intrinsic_curveVelocity_eq_deriv, smul_apply, smul_eq_mul, ho, mul_zero]

end PoincareMT
