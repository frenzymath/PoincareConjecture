import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import Mathlib.Analysis.Calculus.FDeriv.Add

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M28.tube

def cylinderScalarCoordinateEquiv :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] RoundCylinderCoordinates :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

theorem cylinderScalarCoordinateEquiv_apply (v : EuclideanSpace ℝ (Fin 3)) :
    cylinderScalarCoordinateEquiv v = (WithLp.toLp 2 ![v 0, v 1], v 2) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

theorem cylinderScalarCoordinateEquiv_basis (i : Fin 3) :
    cylinderScalarCoordinateEquiv (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      roundCylinderCoordinateBasis i := by
  rw [cylinderScalarCoordinateEquiv_apply]
  apply Prod.ext
  · ext j
    fin_cases i <;> fin_cases j <;>
      simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]
  · fin_cases i <;>
      simp [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply]

def cylinderScalarCoordinates (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    RoundCylinderCoordinates :=
  cylinderScalarCoordinateEquiv x + (0, s)

@[simp] theorem cylinderScalarCoordinates_zero (s : ℝ) :
    cylinderScalarCoordinates s 0 = (0, s) := by
  simp [cylinderScalarCoordinates]

theorem cylinderScalarCoordinates_hasFDerivAt (s : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (cylinderScalarCoordinates s)
      cylinderScalarCoordinateEquiv.toContinuousLinearMap x := by
  exact cylinderScalarCoordinateEquiv.hasFDerivAt.add_const (0, s)

theorem contDiff_cylinderScalarCoordinates (s : ℝ) :
    ContDiff ℝ ∞ (cylinderScalarCoordinates s) :=
  cylinderScalarCoordinateEquiv.contDiff.add contDiff_const

end PoincareConjecture.M28.tube
