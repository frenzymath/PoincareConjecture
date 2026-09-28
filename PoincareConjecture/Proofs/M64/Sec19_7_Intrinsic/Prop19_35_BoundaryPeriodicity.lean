import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryParameters
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem periodic_deriv {f : ℝ → AnnulusCoordinates} {P : ℝ}
    (hf : Function.Periodic f P) : Function.Periodic (deriv f) P := by
  intro x
  have hshift : (fun y => f (y + P)) = f := funext hf
  rw [← deriv_comp_add_const, hshift]

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

theorem m64Intrinsic_boundaryUnitTangent_periodic
    (N : IntrinsicAnnulus) (radius : ℝ) :
    Function.Periodic (intrinsicBoundaryUnitTangent N.metric radius) rampPeriod := by
  intro x
  simp only [intrinsicBoundaryUnitTangent, m64Intrinsic_curveVelocity_eq_deriv,
    m64Intrinsic_boundarySpeed_periodic N radius x,
    periodic_deriv (m64Intrinsic_boundary_periodic radius) x]

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

end PoincareConjecture
