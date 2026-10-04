import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Canonical.Neck.CanonicalNeckPhysicalAssembly
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.CanonicalGeometry.CapMetricScalingNeck

/-!
# Physical scaling of an actual normalized strong-neck family

The literal inverse metric scaling gives the source neck scale required
by the existing physical assembler. Every cylinder map and its clock
are preserved. MT Definition 9.78 and Proposition 17.1, pp. 407-408;
limit-canonical-neck-control.md, G.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin Q : ℝ} {g : RiemannianMetric 3 C.carrier}

private theorem physical_neck_of_scale_eq
    (N : EpsilonNeck g) (hscale : N.scale⁻¹ ^ 2 = Q)
    (e : SurgeryFlowCylinder F C origin Q (Ioc (-1 : ℝ) 0) N.carrier)
    (hscalar : (F.connection (origin + 0 / Q)).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) N.center) =
        N.connection.scalarCurvature N.center)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e N.coordinate_map)) :
    ∃ S : SurgeryStrongNeck F (origin + 0 / Q) N.epsilon,
      S.neck.center = e.forward 0 (by constructor <;> norm_num) N.center := by
  subst Q
  exact Proofs.M47.exists_physical_strong_neck_of_family N e hscalar hfamily

/-- An actual normalized source family and the exact selected scalar
give a physical strong neck at that same cylinder image point. -/
theorem limitCanonical_exists_physical_neck
    (N : EpsilonNeck g) (hNscale : N.scale = 1)
    (e : SurgeryFlowCylinder F C origin Q (Ioc (-1 : ℝ) 0) N.carrier)
    (hphysical : (F.connection (origin + 0 / Q)).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) N.center) = Q)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e N.coordinate_map)) :
    ∃ S : SurgeryStrongNeck F (origin + 0 / Q) N.epsilon,
      S.neck.center = e.forward 0 (by constructor <;> norm_num) N.center := by
  let N' := N.scaleMetric Q⁻¹ (inv_pos.mpr e.scale_pos)
  have hscale : N'.scale⁻¹ ^ 2 = Q := by
    change (Real.sqrt Q⁻¹ * N.scale)⁻¹ ^ 2 = Q
    rw [hNscale, mul_one, inv_pow, Real.sq_sqrt (inv_pos.mpr e.scale_pos).le, inv_inv]
  have hnorm : N.scale⁻¹ ^ 2 = N.connection.scalarCurvature N.center := by
    rw [N.scale_eq_scalar, inv_pow,
      ← Real.rpow_mul_natCast N.scalar_center_pos.le (-1 / 2 : ℝ) 2]
    norm_num [Real.rpow_neg_one]
  have hNscalar : N.connection.scalarCurvature N.center = 1 := by
    simpa only [hNscale, inv_one, one_pow] using hnorm.symm
  have hscaled : N'.connection.scalarCurvature N'.center = Q := by
    change (M13.scaleLeviCivitaData N.connection Q⁻¹
      (inv_pos.mpr e.scale_pos)).scalarCurvature N.center = Q
    rw [M13.scaleLeviCivitaData_scalarCurvature, hNscalar, one_div, inv_inv]
  exact physical_neck_of_scale_eq N' hscale e (hphysical.trans hscaled.symm) hfamily

end PoincareMT.M47
