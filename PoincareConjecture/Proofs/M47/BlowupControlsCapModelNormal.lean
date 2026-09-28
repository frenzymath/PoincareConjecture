import PoincareConjecture.Proofs.M47.BlowupControlsCapCurvatureDifference
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCurvature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private noncomputable def modelConnectionBilinear
    {g : RiemannianMetric 3 E₃} (D : LeviCivitaData g) (x : E₃) :
    E₃ →ₗ[ℝ] E₃ →ₗ[ℝ] E₃ :=
  LinearMap.mk₂ ℝ (fun u v => D.euclideanConnection u v x)
    (fun u v w => congrFun (D.euclideanConnection_add_left u v w) x)
    (fun c u v => congrFun (D.euclideanConnection_smul_left c u v) x)
    (fun u v w => congrFun (D.euclideanConnection_add_right u v w) x)
    (fun c u v => congrFun (D.euclideanConnection_smul_right c u v) x)

theorem cap_model_connection_normal (t : ℝ) (ht : t < 1)
    (D : LeviCivitaData (M35.cylinderEuclideanMetric t ht))
    (q : UnitTwoSphere) (s : ℝ) (u v : E₃) :
    D.euclideanConnection u v (M35.cylinderCoordinateEquiv.symm (0, s)) = 0 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let p := M35.cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  have hz : modelConnectionBilinear D p = 0 := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact M35.cylinder_connection_center t ht D q s i j
  exact congrArg (fun L : E₃ →ₗ[ℝ] E₃ →ₗ[ℝ] E₃ => L u v) hz

end PoincareConjecture.M47
