import PoincareConjecture.Proofs.M35.Thm12_28.EuclideanCylinder
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderChristoffel
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Convergence

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35

theorem cylinderEuclideanMetric_inner_basis (u : ℝ) (hu : u < 1)
    (p v : EuclideanSpace ℝ (Fin 3)) (a : Fin 3) :
    (cylinderEuclideanMetric u hu).inner p v (EuclideanSpace.basisFun (Fin 3) ℝ a) =
      ![32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2,
        32 * (1 - u) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2, 1] a * v a := by
  change cylinderEuclideanCoefficients u p v (EuclideanSpace.basisFun (Fin 3) ℝ a) = _
  rw [cylinderEuclideanCoefficients_apply, cylinderCoordinateEquiv_basis]
  fin_cases a <;> simp [roundCylinderCoordinateBasis, EuclideanSpace.inner_single_right,
    cylinderCoordinateEquiv_fst, cylinderCoordinateEquiv_snd]

theorem fderiv_cylinderEuclideanMetric_basis (u : ℝ) (hu : u < 1) (q : UnitTwoSphere)
    (p : EuclideanSpace ℝ (Fin 3)) (a b k : Fin 3) :
    fderiv ℝ (fun p : EuclideanSpace ℝ (Fin 3) => (cylinderEuclideanMetric u hu).inner p
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b))
        p (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      fderiv ℝ (fun p : RoundCylinderCoordinates =>
        roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)
        (cylinderCoordinateEquiv p) (roundCylinderCoordinateBasis k) := by
  simp_rw [cylinderEuclideanMetric_basis u hu q]
  have hd := ((contDiff_roundCylinderGram u q a b).differentiable (by simp)
    (cylinderCoordinateEquiv p)).hasFDerivAt.comp p cylinderCoordinateEquiv.hasFDerivAt
  convert! congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ =>
    L (EuclideanSpace.basisFun (Fin 3) ℝ k)) hd.fderiv using 1
  exact congrArg (fderiv ℝ (fun p : RoundCylinderCoordinates =>
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)
      (cylinderCoordinateEquiv p)) (cylinderCoordinateEquiv_basis k).symm

theorem cylinder_connection_component (u : ℝ) (hu : u < 1)
    (D : LeviCivitaData (cylinderEuclideanMetric u hu)) (q : UnitTwoSphere)
    (p : EuclideanSpace ℝ (Fin 3)) (a b d : Fin 3) :
    (D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ b)
      (EuclideanSpace.basisFun (Fin 3) ℝ d) p) a =
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (cylinderCoordinateEquiv p) a b d := by
  have hk := D.inner_connection_const p (EuclideanSpace.basisFun (Fin 3) ℝ b)
    (EuclideanSpace.basisFun (Fin 3) ℝ d) (EuclideanSpace.basisFun (Fin 3) ℝ a)
  change 2 * (cylinderEuclideanMetric u hu).inner p
    (D.euclideanConnection (EuclideanSpace.basisFun (Fin 3) ℝ b)
      (EuclideanSpace.basisFun (Fin 3) ℝ d) p) (EuclideanSpace.basisFun (Fin 3) ℝ a) = _ at hk
  rw [cylinderEuclideanMetric_inner_basis] at hk
  simp_rw [fderiv_cylinderEuclideanMetric_basis u hu q] at hk
  have hsymm : (fun p : RoundCylinderCoordinates =>
      roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b) =
      fun p => roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p b a := by
    funext p
    by_cases hab : a = b
    · subst b
      rfl
    · simp [roundCylinderGram_eq, Matrix.diagonal, hab, Ne.symm hab]
  rw [hsymm] at hk
  unfold roundCylinderChristoffel
  rw [roundCylinderGram_inv_eq hu]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [← hk]
  have ht : 1 - u ≠ 0 := by linarith
  have hp : ‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  fin_cases a <;> norm_num <;> field_simp

end PoincareConjecture.M35
