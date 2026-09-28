import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNativeMetric
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialModelMetric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

open M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem source_initial_centered_tensor_evaluation
    (B : RoundCylinderTwoTensor) (q : UnitTwoSphere) (s : ℝ) (p : E)
    (L : V →L[ℝ] V →L[ℝ] ℝ)
    (hL : ∀ v w, L v w = B (centeredCylinderLift q s p) v w) (v w : E) :
    centeredCylinderMetric B q s p v w =
      B (centeredCylinderLift q s p)
        (mfderiv (𝓡 3) IC (centeredCylinderLift q s) p v)
        (mfderiv (𝓡 3) IC (centeredCylinderLift q s) p w) := by
  let D : E →L[ℝ] V := mfderiv (𝓡 3) IC (centeredCylinderLift q s) p
  have hcoeff : centeredCylinderMetric B q s p = L.bilinearComp D D := by
    apply euclideanThree_bilinear_ext
    intro i j
    rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
    have hcoord : cylinderEuclideanEquiv p + (0, s) =
        (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
      apply Prod.ext
      · exact add_zero _
      · rfl
    rw [hcoord]
    change roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) i j =
        L (D (EuclideanSpace.basisFun (Fin 3) ℝ i)) (D (EuclideanSpace.basisFun (Fin 3) ℝ j))
    rw [hL]
    have hd (k : Fin 3) : D (EuclideanSpace.basisFun (Fin 3) ℝ k) =
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
          (cylinderHorizontalProjection p)
          (cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k)),
          cylinderHeightCovector (EuclideanSpace.basisFun (Fin 3) ℝ k)) :=
      centeredCylinderLift_mfderiv q s p _
    rw [hd i, hd j]
    have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
        (roundCylinderCoordinateBasis k).1 := congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
    simp only [roundCylinderTensorCoefficient, cylinderHeightCovector_basis, hP]
    rfl
  rw [hcoeff]
  exact hL (D v) (D w)



theorem source_initial_centered_metric_bounds
    {epsilon u : ℝ} (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 2)
    (hu : u ∈ Icc (-1 : ℝ) 0) {B : RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose epsilon u B)
    (q : UnitTwoSphere) (s : ℝ) (p : E)
    (hp : cylinderHeightCovector p + s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hhorizontal : ‖cylinderHorizontalProjection p‖ ≤ 1)
    (L : V →L[ℝ] V →L[ℝ] ℝ)
    (hL : ∀ v w, L v w = B (centeredCylinderLift q s p) v w) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ centeredCylinderMetric B q s p v v ∧
      centeredCylinderMetric B q s p v v ≤ 6 * ‖v‖ ^ 2 := by
  have hnative := source_initial_native_metric_bounds hepsilon hsmall
    (hu.2.trans_lt (by norm_num)) hclose (centeredCylinderLift q s p) hp L hL
    (mfderiv (𝓡 3) IC (centeredCylinderLift q s) p v)
  rw [source_initial_model_pullback,
    ← source_initial_centered_tensor_evaluation B q s p L hL v v] at hnative
  have hmodel := source_initial_model_metric_bounds hu hhorizontal v
  constructor <;> linarith only [hnative.1, hnative.2, hmodel.1, hmodel.2]

end PoincareConjecture.M47
