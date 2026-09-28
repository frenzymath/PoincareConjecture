import PoincareConjecture.Proofs.M35.Thm12_28.CylinderLeviCivita
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35



theorem fderiv_cylinder_connection_component (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (p : EuclideanSpace ℝ (Fin 3)) (i a b d : Fin 3) :
    (fderiv ℝ (D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ b)
      (EuclideanSpace.basisFun (Fin 3) ℝ d)) p (EuclideanSpace.basisFun (Fin 3) ℝ i)) a =
      fderiv ℝ (fun p : RoundCylinderCoordinates =>
        roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d)
        (cylinderCoordinateEquiv p) (roundCylinderCoordinateBasis i) := by
  have hv := ((EuclideanSpace.proj a : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt).comp p
    ((D.contDiffAt_euclideanConnection p (EuclideanSpace.basisFun (Fin 3) ℝ b)
      (EuclideanSpace.basisFun (Fin 3) ℝ d)).differentiableAt (by simp)).hasFDerivAt
  have heval : fderiv ℝ (fun p =>
      (D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ b)
        (EuclideanSpace.basisFun (Fin 3) ℝ d) p) a) p
          (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      (fderiv ℝ (D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ b)
        (EuclideanSpace.basisFun (Fin 3) ℝ d)) p
          (EuclideanSpace.basisFun (Fin 3) ℝ i)) a := by
    convert! congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin 3) ℝ i)) hv.fderiv using 1
  rw [← heval]
  simp_rw [cylinder_connection_component u hu D q]
  have hd := ((contDiff_roundCylinderChristoffel hu q a b d).differentiable (by simp)
    (cylinderCoordinateEquiv p)).hasFDerivAt.comp p cylinderCoordinateEquiv.hasFDerivAt
  convert! congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin 3) ℝ i)) hd.fderiv using 1
  exact congrArg (fderiv ℝ (fun p : RoundCylinderCoordinates =>
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d)
      (cylinderCoordinateEquiv p)) (cylinderCoordinateEquiv_basis i).symm



theorem cylinder_connection_center (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (s : ℝ) (b d : Fin 3) :
    D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ b)
      (EuclideanSpace.basisFun (Fin 3) ℝ d) (cylinderCoordinateEquiv.symm (0, s)) = 0 := by
  ext a
  change (D.euclideanConnection _ _ _) a = 0
  rw [cylinder_connection_component u hu D q, ContinuousLinearEquiv.apply_symm_apply,
    roundCylinderChristoffel_center]




theorem cylinder_curvature_component_center (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (s : ℝ) (i j l a : Fin 3) :
    EuclideanSpace.proj a (D.curvature (cylinderCoordinateEquiv.symm (0, s))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
      (EuclideanSpace.basisFun (Fin 3) ℝ l)) =
      inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis i).1 *
        inner ℝ (roundCylinderCoordinateBasis j).1 (roundCylinderCoordinateBasis l).1 -
      inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis j).1 *
        inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis l).1 := by
  let p := cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  have hz (v : EuclideanSpace ℝ (Fin 3)) : D.euclideanConnection v 0 p = 0 := by
    have h := congrArg (fun f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) => f p)
      (D.euclideanConnection_smul_right (0 : ℝ) v (0 : EuclideanSpace ℝ (Fin 3)))
    simpa only [zero_smul, Pi.zero_apply] using h
  have hc := D.curvature_eq_euclideanConnection p (EuclideanSpace.basisFun (Fin 3) ℝ i)
    (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ l)
  rw [cylinder_connection_center u hu D q s j l,
    cylinder_connection_center u hu D q s i l, hz, hz, add_zero, add_zero] at hc
  have hca := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v a) hc
  simp only [PiLp.sub_apply] at hca
  refine Eq.trans (by exact hca) ?_
  rw [fderiv_cylinder_connection_component u hu D q,
    fderiv_cylinder_connection_component u hu D q]
  simp only [p, ContinuousLinearEquiv.apply_symm_apply,
    fderiv_roundCylinderChristoffel_center hu]
  simp only [real_inner_comm]
  ring




theorem cylinder_curvatureTensor_center (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (s : ℝ) (i j k l : Fin 3) :
    D.curvatureTensor (cylinderCoordinateEquiv.symm (0, s))
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
      (EuclideanSpace.basisFun (Fin 3) ℝ k) (EuclideanSpace.basisFun (Fin 3) ℝ l) =
      2 * (1 - u) *
        (inner ℝ (roundCylinderCoordinateBasis k).1 (roundCylinderCoordinateBasis i).1 *
          inner ℝ (roundCylinderCoordinateBasis j).1 (roundCylinderCoordinateBasis l).1 -
        inner ℝ (roundCylinderCoordinateBasis k).1 (roundCylinderCoordinateBasis j).1 *
          inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis l).1) := by
  let p := cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  let w : Fin 3 → ℝ :=
    ![32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2,
      32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2, 1]
  have hg := cylinderEuclideanMetric_inner_basis u hu p
    (D.curvature p (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) (EuclideanSpace.basisFun (Fin 3) ℝ l)) k
  have hr := congrArg (fun r : ℝ => w k * r)
    (cylinder_curvature_component_center u hu D q s i j l k)
  refine Eq.trans (by exact hg) (Eq.trans (by exact hr) ?_)
  simp only [w, p, ContinuousLinearEquiv.apply_symm_apply, norm_zero, zero_pow (by omega : 2 ≠ 0),
    zero_add]
  fin_cases k <;> norm_num [roundCylinderCoordinateBasis] <;> (left; ring)

end PoincareConjecture.M35
