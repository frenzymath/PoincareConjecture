import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Boundary.Parameters
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Periodicity of intrinsic boundary length and turning densities

The coordinate circle and its derivatives are periodic. The actual metric
speed and covariant turning density therefore have the same period, with
no bound on the metric coefficients or choice of an angular cut.

Context: Morgan--Tian Proposition 19.35 and Claim 19.57, printed pp. 467 and
479-480; the cyclic cover and its factor-two budget are the recorded repair.
Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-cyclic-focusing.md.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem periodic_deriv {f : ℝ → AnnulusCoordinates} {P : ℝ}
    (hf : Function.Periodic f P) : Function.Periodic (deriv f) P := by
  intro x
  have hshift : (fun y => f (y + P)) = f := funext hf
  rw [← deriv_comp_add_const, hshift]

/-- The actual boundary speed in Proposition 19.35 has the coordinate
circle's period; see `derivations/2026-09-25-cyclic-focusing.md`. -/
theorem m64Intrinsic_boundarySpeed_periodic
    (N : IntrinsicAnnulus) (radius : ℝ) :
    Function.Periodic (intrinsicBoundarySpeed N.metric radius) rampPeriod := by
  intro x
  simp only [intrinsicBoundarySpeed, m64Intrinsic_curveVelocity_eq_deriv,
    periodic_deriv (m64Intrinsic_boundary_periodic radius) x]
  change Real.sqrt (N.metric.euclideanCoefficients
    (intrinsicAnnulusBoundary radius (x + rampPeriod)) _ _) =
    Real.sqrt (N.metric.euclideanCoefficients (intrinsicAnnulusBoundary radius x) _ _)
  rw [m64Intrinsic_boundary_periodic radius x]

/-- The boundary unit tangent in Proposition 19.35 is periodic, including the totalized
zero-radius case. Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-cyclic-focusing.md. -/
theorem m64Intrinsic_boundaryUnitTangent_periodic
    (N : IntrinsicAnnulus) (radius : ℝ) :
    Function.Periodic (intrinsicBoundaryUnitTangent N.metric radius) rampPeriod := by
  intro x
  simp only [intrinsicBoundaryUnitTangent, m64Intrinsic_curveVelocity_eq_deriv,
    m64Intrinsic_boundarySpeed_periodic N radius x,
    periodic_deriv (m64Intrinsic_boundary_periodic radius) x]

/-- The absolute-turning density in Proposition 19.35 is periodic on every nondegenerate
coordinate circle. Source/construction:
proof-work/tasks/M64/derivations/2026-09-25-cyclic-focusing.md. -/
theorem m64Intrinsic_turning_density_periodic
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0) :
    Function.Periodic
      (fun x => intrinsicGeodesicCurvature N.metric N.connection radius x *
        intrinsicBoundarySpeed N.metric radius x) rampPeriod := by
  intro x
  have hγ := m64Intrinsic_contDiff_boundary radius
  have hT := m64Intrinsic_contDiff_boundaryUnitTangent N hradius
  simp only [m64Intrinsic_turning_density N hradius,
    m64Intrinsic_pullback_model N hγ hT,
    m64Intrinsic_boundary_periodic radius x,
    periodic_deriv (m64Intrinsic_boundary_periodic radius) x,
    m64Intrinsic_boundaryUnitTangent_periodic N radius x,
    periodic_deriv (m64Intrinsic_boundaryUnitTangent_periodic N radius) x]
  change Real.sqrt (N.metric.euclideanCoefficients
    (intrinsicAnnulusBoundary radius (x + rampPeriod)) _ _) =
    Real.sqrt (N.metric.euclideanCoefficients (intrinsicAnnulusBoundary radius x) _ _)
  rw [m64Intrinsic_boundary_periodic radius x]

end PoincareMT
