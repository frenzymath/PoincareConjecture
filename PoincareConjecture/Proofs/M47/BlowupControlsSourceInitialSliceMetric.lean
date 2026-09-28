import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialReadout
import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothetyRicci









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M36 M44 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
  {origin scale : ℝ} {I : Set ℝ}
  (e : SurgeryFlowCylinder F C origin scale I N.carrier)



theorem source_neck_slice_metric_of_coefficients (s : ℝ) (hs : s ∈ I)
    (q : UnitTwoSphere) (g1 : RiemannianMetric 3 E) {y : E}
    (hy : y ∈ centeredNeckDomain N 0)
    (hcoeff : ∀ i j : Fin 3,
      g1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient (surgeryCylinderPullback e N.coordinate_map s)
        (chartAt E2 q) (M35.cylinderCoordinateEquiv y) i j)
    (v w : TangentSpace (𝓡 3) y) :
    let f := e.forward s hs ∘ centeredNeckLift N q 0
    g1.inner y v w = scale * (F.metric (origin + s / scale)).inner (f y)
      (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) := by
  let f := e.forward s hs ∘ centeredNeckLift N q 0
  have hmem : centeredNeckLift N q 0 y ∈ N.carrier := centeredNeckLift_mem N q 0 hy
  have hnative := (centeredNeckLift_contMDiffAt N q 0 hy).mdifferentiableAt (by simp)
  have hforward := ((e.forward_smooth s hs).contMDiffAt
    (N.carrier_open.mem_nhds hmem)).mdifferentiableAt (by simp)
  have hchain : mfderiv (𝓡 3) (𝓡 3) f y =
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (centeredNeckLift N q 0 y)).comp
        (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q 0) y) :=
    mfderiv_comp y hforward hnative
  have hmetric : g1.inner y =
      scale • (F.metric (origin + s / scale)).pullbackCoefficients f y := by
    apply euclideanThree_bilinear_ext
    intro i j
    change g1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      scale * (F.metric (origin + s / scale)).inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y (EuclideanSpace.basisFun (Fin 3) ℝ i))
        (mfderiv (𝓡 3) (𝓡 3) f y (EuclideanSpace.basisFun (Fin 3) ℝ j))
    rw [hcoeff]
    have hcoord : M35.cylinderCoordinateEquiv y =
        (cylinderHorizontalProjection y, cylinderHeightCovector y + 0) := by
      apply Prod.ext
      · rfl
      · exact (add_zero _).symm
    rw [hcoord]
    have hd (k : Fin 3) : mfderiv (𝓡 3) (𝓡 3) f y
        (EuclideanSpace.basisFun (Fin 3) ℝ k) =
        mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) (centeredNeckLift N q 0 y)
          (mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N q 0) y
            (EuclideanSpace.basisFun (Fin 3) ℝ k)) :=
      congrArg (fun A => A (EuclideanSpace.basisFun (Fin 3) ℝ k)) hchain
    rw [hd i, hd j, centeredNeckLift_mfderiv N q 0 hy,
      centeredNeckLift_mfderiv N q 0 hy]
    have hP (k : Fin 3) : cylinderHorizontalProjection (EuclideanSpace.basisFun (Fin 3) ℝ k) =
        (roundCylinderCoordinateBasis k).1 :=
      congrArg Prod.fst (cylinderEuclideanEquiv_basis k)
    simp only [roundCylinderTensorCoefficient, surgeryCylinderPullback, dif_pos hs,
      SurgeryFlowCylinder.pullbackInner, cylinderHeightCovector_basis, hP,
      f, Function.comp_apply, centeredNeckLift, centeredCylinderLift]
  exact congrArg (fun B => B v w) hmetric



theorem source_neck_slice_ricci_of_coefficients (s : ℝ) (hs : s ∈ I)
    (q : UnitTwoSphere) (g1 : RiemannianMetric 3 E) (D1 : LeviCivitaData g1)
    {W : Set E} (hW : IsOpen W)
    (hcoeff : ∀ y ∈ W, ∀ i j : Fin 3,
      g1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ j) =
      roundCylinderTensorCoefficient (surgeryCylinderPullback e N.coordinate_map s)
        (chartAt E2 q) (M35.cylinderCoordinateEquiv y) i j)
    {y : E} (hyW : y ∈ W) (hy : y ∈ centeredNeckDomain N 0)
    (v w : TangentSpace (𝓡 3) y) :
    let f := e.forward s hs ∘ centeredNeckLift N q 0
    D1.ricci y v w = (F.connection (origin + s / scale)).ricci (f y)
      (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) := by
  let f := e.forward s hs ∘ centeredNeckLift N q 0
  have hU : IsOpen (W ∩ centeredNeckDomain N 0) := hW.inter (centeredNeckDomain_isOpen N 0)
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (W ∩ centeredNeckDomain N 0) := by
    intro z hz
    have hmem := centeredNeckLift_mem N q 0 hz.2
    have hforward := (e.forward_smooth s hs).contMDiffAt (N.carrier_open.mem_nhds hmem)
    exact (hforward.comp z (centeredNeckLift_contMDiffAt N q 0 hz.2)).contMDiffWithinAt
  exact D1.ricci_eq_of_local_homothety (F.connection (origin + s / scale)) e.scale_pos hU hf
    (fun z hz v w => source_neck_slice_metric_of_coefficients N e s hs q g1 hz.2
      (hcoeff z hz.1) v w) ⟨hyW, hy⟩ v w

end PoincareConjecture.M47
