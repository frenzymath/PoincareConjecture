import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_TransitionChart
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_CylinderCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CoefficientTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem pullbackCoefficients_comp_bilinear
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) {f : E → M} {a : E → E} {x : E}
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (a x)) (ha : ContDiffAt ℝ ∞ a x) :
    g.pullbackCoefficients (f ∘ a) x =
      (g.pullbackCoefficients f (a x)).bilinearComp (fderiv ℝ a x) (fderiv ℝ a x) := by
  ext v w
  change g.inner (f (a x)) (mfderiv (𝓡 3) (𝓡 3) (f ∘ a) x v)
    (mfderiv (𝓡 3) (𝓡 3) (f ∘ a) x w) = _
  rw [mfderiv_comp x (hf.mdifferentiableAt (by simp))
    (ha.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
  rfl

theorem centeredCylinderMetric_smul (r : ℝ) (B : RoundCylinderTwoTensor)
    (q : UnitTwoSphere) (s : ℝ) :
    centeredCylinderMetric (fun z v w => r * B z v w) q s =
      fun p => r • centeredCylinderMetric B q s p := by
  funext p
  apply euclideanThree_bilinear_ext
  intro i j
  change centeredCylinderMetric (fun z v w => r * B z v w) q s p
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) =
    r * centeredCylinderMetric B q s p
      (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
  simp only [centeredCylinderMetric, centeredCylinderBilinear_basis,
    roundCylinderTensorCoefficient]

end M45

namespace M45NeckGluingInput

open M36 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)

theorem recentCenteredMap_pullbackCoefficients
    (hpos : 0 < beta * epsilon) (hsmall : beta * epsilon < 1 / 2)
    (z : RoundCylinderSpace) (t : ℝ) {p : E}
    (hp : p ∈ centeredNeckDomain (I.recentNeck hpos hsmall) z.2) :
    (I.recent_flow.metric t).pullbackCoefficients (I.recentCenteredMap z) p =
      centeredCylinderMetric
        (roundCylinderPullback (I.recent_flow.metric t) I.recent_patch.coordinate) z.1 z.2 p :=
  centeredCylinder_pullbackCoefficients _ _ _ _ _
    (I.recent_patch.coordinate_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp⟩))

theorem olderCenteredMap_normalizedCoefficients (z : RoundCylinderSpace) (tau : ℝ) {p : E}
    (hp : p ∈ centeredNeckDomain I.older_neck.neck (I.olderCenteredCoordinate z).2) :
    centeredCylinderMetric
      (fun y v w => I.older_neck.neck.scale⁻¹ ^ 2 *
        roundCylinderPullback
          (I.older_flow.metric (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2))
          I.older_neck.neck.coordinate_map y v w)
      (I.olderCenteredCoordinate z).1 (I.olderCenteredCoordinate z).2 p =
        I.older_neck.neck.scale⁻¹ ^ 2 •
          (I.older_flow.metric
            (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2)).pullbackCoefficients
              (I.olderCenteredMap z) p := by
  rw [centeredCylinderMetric_smul]
  exact congrArg (fun L => I.older_neck.neck.scale⁻¹ ^ 2 • L)
    (centeredCylinder_pullbackCoefficients
      (I.older_flow.metric (-I.recent_duration + tau * I.older_neck.neck.scale ^ 2))
      I.older_neck.neck.coordinate_map (I.olderCenteredCoordinate z).1
      (I.olderCenteredCoordinate z).2 p
      (neck_coordinate_contMDiffAt I.older_neck.neck ⟨mem_univ _, hp⟩)).symm

theorem joining_centered_coefficients
    (hpos : 0 < beta * epsilon) (hsmall : beta * epsilon < 1 / 2)
    (z : RoundCylinderSpace) {p : E}
    (hp : p ∈ centeredNeckDomain (I.recentNeck hpos hsmall) z.2) :
    (I.older_flow.metric (-I.recent_duration)).pullbackCoefficients
      (I.identify ∘ I.recentCenteredMap z) p =
        (I.recent_flow.metric (-I.recent_duration)).pullbackCoefficients
          (I.recentCenteredMap z) p := by
  let N := I.recentNeck hpos hsmall
  have hm : I.recentCenteredMap z p ∈ I.recent_patch.carrier :=
    centeredNeckLift_mem N z.1 z.2 hp
  exact M44.pullbackCoefficients_eq_of_metric_germ _ _
    ((I.identify_smooth.contMDiffAt (I.recent_patch.carrier_open.mem_nhds hm)).mdifferentiableAt
      (by simp))
    ((centeredNeckLift_contMDiffAt N z.1 z.2 hp).mdifferentiableAt (by simp))
    (Filter.EventuallyEq.refl _ _) (I.joining_metric _ hm)

end M45NeckGluingInput

end PoincareConjecture
