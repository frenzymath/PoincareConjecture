import PoincareConjecture.Proofs.M36.CenteredNeckMetric










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M45

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)




theorem centeredCylinder_pullbackCoefficients
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (f : RoundCylinderSpace → M)
    (q : UnitTwoSphere) (s : ℝ) (p : E)
    (hf : ContMDiffAt IC (𝓡 3) ∞ f (centeredCylinderLift q s p)) :
    g.pullbackCoefficients (f ∘ centeredCylinderLift q s) p =
      centeredCylinderMetric (roundCylinderPullback g f) q s p := by
  apply euclideanThree_bilinear_ext
  intro i j
  rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
  have hcoord : cylinderEuclideanEquiv p + (0, s) =
      (cylinderHorizontalProjection p, cylinderHeightCovector p + s) := by
    apply Prod.ext
    · exact add_zero _
    · rfl
  rw [hcoord]
  have hd := mfderiv_comp p (hf.mdifferentiableAt (by simp))
    ((centeredCylinderLift_contMDiff q s p).mdifferentiableAt (by simp))
  have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
      (roundCylinderCoordinateBasis k).1 :=
    congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
  change g.inner _
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ centeredCylinderLift q s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i))
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ centeredCylinderLift q s) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [hd]
  change g.inner (f (centeredCylinderLift q s p))
      (mfderiv IC (𝓡 3) f (centeredCylinderLift q s p)
        (mfderiv (𝓡 3) IC (centeredCylinderLift q s) p
          (EuclideanSpace.basisFun (Fin 3) ℝ i)))
      (mfderiv IC (𝓡 3) f (centeredCylinderLift q s p)
        (mfderiv (𝓡 3) IC (centeredCylinderLift q s) p
          (EuclideanSpace.basisFun (Fin 3) ℝ j))) = _
  rw [centeredCylinderLift_mfderiv, centeredCylinderLift_mfderiv]
  simp only [roundCylinderTensorCoefficient, roundCylinderPullback,
    cylinderHeightCovector_basis, hP]
  rfl




theorem centeredCylinderMetric_coefficient (B : RoundCylinderTwoTensor)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (i j : Fin 3) :
    centeredCylinderMetric B q 0 (cylinderEuclideanEquiv.symm p)
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j := by
  rw [centeredCylinderMetric, centeredCylinderBilinear_basis]
  simp only [ContinuousLinearEquiv.apply_symm_apply, Prod.mk_zero_zero, add_zero]

end PoincareConjecture.M45
