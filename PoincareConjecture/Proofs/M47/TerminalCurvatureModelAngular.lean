import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCurvature
import PoincareConjecture.Proofs.M03.CurvatureTrilinear








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_model_angular_vector
    (D : LeviCivitaData (M35.cylinderEuclideanMetric 0 (by norm_num)))
    (q : UnitTwoSphere) (s : ℝ) (a : ℝ) (ha : a ^ 2 = 1 / 2)
    (e : E ≃L[ℝ] E)
    (he0 : e (EuclideanSpace.basisFun (Fin 3) ℝ 0) =
      a • EuclideanSpace.basisFun (Fin 3) ℝ 0)
    (he1 : e (EuclideanSpace.basisFun (Fin 3) ℝ 1) =
      a • EuclideanSpace.basisFun (Fin 3) ℝ 1) :
    D.curvature (M35.cylinderCoordinateEquiv.symm (0, s))
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 0))
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 1))
      (e (EuclideanSpace.basisFun (Fin 3) ℝ 1)) =
      (1 / 2 : ℝ) • e (EuclideanSpace.basisFun (Fin 3) ℝ 0) := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let p := M35.cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  have hmodel : D.curvature p (b 0) (b 1) (b 1) = b 0 := by
    apply PiLp.ext
    intro i
    change EuclideanSpace.proj i (D.curvature p (b 0) (b 1) (b 1)) = (b 0) i
    rw [M35.cylinder_curvature_component_center 0 (by norm_num) D q s 0 1 1 i]
    fin_cases i <;>
      norm_num [b, roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_left]
  obtain ⟨R, hR⟩ := PoincareConjecture.Proofs.M03.exists_curvature_trilinearMap D p
  rw [he0, he1]
  change D.curvature p (a • b 0) (a • b 1) (a • b 1) = (1 / 2 : ℝ) • (a • b 0)
  rw [← hR]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  rw [hR, hmodel]
  apply congrArg (fun c : ℝ => c • b 0)
  nlinarith only [congrArg (fun c : ℝ => c * a) ha]

end PoincareConjecture.M47
