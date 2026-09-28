import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Euclidean.IntegralEuclideanRelativeHomology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.IntegralCohomologyEvaluation
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.SingularHomology.Cohomology.CompactSupport.IntegralCompactCohomology

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits HomologicalComplex Metric Set TopologicalSpace

namespace Poincare.Topology

private theorem zeroBallHomologyThree_projective (r : Real) (hr : 0 ≤ r) :
    CategoryTheory.Projective (integralSupportHomology
      (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3) := by
  let : Module.Free Int (integralSupportHomology
      (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3) :=
    Module.Free.of_equiv (integralEuclideanBallSupportThreeIso 0 r hr).symm.toLinearEquiv
  infer_instance

theorem integralEuclideanZeroBallCohomology_ne_three_isZero
    (r : Real) (hr : 0 ≤ r) (q : Nat) (hq : q ≠ 3) :
    IsZero (integralSupportCohomology
      (closedBall (0 : EuclideanSpace Real (Fin 3)) r) q) := by
  let C := integralSupportChains (closedBall (0 : EuclideanSpace Real (Fin 3)) r)
  let : CategoryTheory.Projective (C.homology 3) := zeroBallHomologyThree_projective r hr
  let : ∀ n, CategoryTheory.Projective (C.X n) := integralRelativeChains_projective _
  exact moduleComplexDualHomology_isZero 3 C
    (integralEuclideanZeroBallHomology_ne_three_isZero r hr) q hq

def integralEuclideanZeroBallCohomologyEvaluationEquiv
    (r : Real) (hr : 0 ≤ r) :
    integralSupportCohomology (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3 ≃ₗ[Int]
      (integralSupportHomology (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3
        →ₗ[Int] ULift Int) := by
  let C := integralSupportChains (closedBall (0 : EuclideanSpace Real (Fin 3)) r)
  let : CategoryTheory.Projective (C.homology 3) := zeroBallHomologyThree_projective r hr
  let : ∀ n, CategoryTheory.Projective (C.X n) := integralRelativeChains_projective _
  exact integralCohomologyEvaluationEquiv C 3
    (integralEuclideanZeroBallHomology_ne_three_isZero r hr)

theorem integralEuclideanZeroBallCohomologyEvaluationEquiv_apply
    (r : Real) (hr : 0 ≤ r)
    (b : integralSupportCohomology (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3)
    (a : integralSupportHomology (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3) :
    integralEuclideanZeroBallCohomologyEvaluationEquiv r hr b a =
    integralHomologyCohomologyPairing
        (integralSupportChains (closedBall (0 : EuclideanSpace Real (Fin 3)) r)) 3 a b := by
  let C := integralSupportChains (closedBall (0 : EuclideanSpace Real (Fin 3)) r)
  let : CategoryTheory.Projective (C.homology 3) := zeroBallHomologyThree_projective r hr
  let : ∀ n, CategoryTheory.Projective (C.X n) := integralRelativeChains_projective _
  exact integralCohomologyEvaluationEquiv_apply C 3
    (integralEuclideanZeroBallHomology_ne_three_isZero r hr) b a

def integralEuclideanZeroBallCohomologyThreeEquiv (r : Real) (hr : 0 ≤ r) :
    integralSupportCohomology (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3 ≃ₗ[Int]
      ULift Int :=
  (integralEuclideanZeroBallCohomologyEvaluationEquiv r hr).trans
    ((LinearEquiv.arrowCongr
      ((integralEuclideanBallSupportThreeIso 0 r hr).toLinearEquiv.trans ULift.moduleEquiv)
      (LinearEquiv.refl Int (ULift Int))).trans
        (LinearMap.ringLmapEquivSelf Int Int (ULift Int)))

theorem integralEuclideanZeroBallCohomologyThreeEquiv_apply
    (r : Real) (hr : 0 ≤ r)
    (b : integralSupportCohomology (closedBall (0 : EuclideanSpace Real (Fin 3)) r) 3) :
    integralEuclideanZeroBallCohomologyThreeEquiv r hr b =
      integralHomologyCohomologyPairing
        (integralSupportChains (closedBall (0 : EuclideanSpace Real (Fin 3)) r)) 3
          ((integralEuclideanBallSupportThreeIso 0 r hr).inv (ULift.up 1)) b := by
  exact integralEuclideanZeroBallCohomologyEvaluationEquiv_apply r hr b _

end Poincare.Topology
