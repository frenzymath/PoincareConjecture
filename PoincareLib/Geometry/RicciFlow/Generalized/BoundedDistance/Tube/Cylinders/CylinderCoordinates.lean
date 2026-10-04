import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Fixed Euclidean coordinates for the literal cylinder

The frozen sphere-plane/axis basis is the image of the Euclidean three-space
basis under one fixed continuous linear equivalence. Its target has the
ordinary product norm, so no isometry claim is made. Axial translation then
places a chosen cylinder point at the coordinate origin. See Morgan--Tian
Definition 2.16, p. 30, and the M28 cylinder-scalar-readout derivation.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M28.tube

/-- Fixed coordinates sending the Euclidean basis to the frozen cylinder
basis of Definition 2.16, printed p. 30. -/
def cylinderScalarCoordinateEquiv :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] RoundCylinderCoordinates :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)))

/-- The fixed map keeps the first two entries and the axial third entry. -/
theorem cylinderScalarCoordinateEquiv_apply (v : EuclideanSpace ℝ (Fin 3)) :
    cylinderScalarCoordinateEquiv v = (WithLp.toLp 2 ![v 0, v 1], v 2) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · rfl

/-- Exact basis correspondence for the frozen coefficient function. -/
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

/-- Translate only the axis after the fixed coordinate equivalence. -/
def cylinderScalarCoordinates (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    RoundCylinderCoordinates :=
  cylinderScalarCoordinateEquiv x + (0, s)

/-- The translated origin is the literal chosen cylinder centre `(0,s)`. -/
@[simp] theorem cylinderScalarCoordinates_zero (s : ℝ) :
    cylinderScalarCoordinates s 0 = (0, s) := by
  simp [cylinderScalarCoordinates]

/-- Translation leaves the fixed differential unchanged. -/
theorem cylinderScalarCoordinates_hasFDerivAt (s : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (cylinderScalarCoordinates s)
      cylinderScalarCoordinateEquiv.toContinuousLinearMap x := by
  exact cylinderScalarCoordinateEquiv.hasFDerivAt.add_const (0, s)

/-- The translated coordinates are smooth without a point-dependent bound. -/
theorem contDiff_cylinderScalarCoordinates (s : ℝ) :
    ContDiff ℝ ∞ (cylinderScalarCoordinates s) :=
  cylinderScalarCoordinateEquiv.contDiff.add contDiff_const

end PoincareMT.M28.tube
