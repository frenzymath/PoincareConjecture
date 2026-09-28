import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSlabCoefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem source_initial_actual_slab_coefficients
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    {origin scale : ℝ} {I : Set ℝ}
    (U : TopologicalSpace.Opens C.carrier)
    (D : SurgeryFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (gU : RiemannianMetric 3 U)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace (𝓡 3) x,
      gU.inner x v w = D.pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (theta : UnitTwoSphere) (c : ℝ)
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞)
    (hsource : Phi.source = Metric.ball 0 (1 / 2))
    (hmap : ∀ p ∈ Metric.ball (0 : E) (1 / 2),
      (Phi p).val = centeredNeckLift N theta c p)
    (hdomain : Metric.ball (0 : E) (1 / 2) ⊆ centeredNeckDomain N c)
    {p : E} (hp : p ∈ Metric.ball 0 (1 / 2)) :
    gU.pullbackCoefficients Phi p =
      centeredCylinderMetric (surgeryCylinderPullback D N.coordinate_map s) theta c p := by
  obtain ⟨L, hL⟩ := source_initial_cylinder_tensor_bilinear D N.coordinate_map s hs
    (centeredCylinderLift theta c p)
  have hd := source_initial_neck_chart_differential N U theta c Phi hsource hmap hp
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change gU.inner (Phi p) (mfderiv (𝓡 3) (𝓡 3) Phi p v)
    (mfderiv (𝓡 3) (𝓡 3) Phi p w) = _
  rw [hmetric]
  have hv := congrArg (fun A => A v) hd
  have hw := congrArg (fun A => A w) hd
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Phi p)
    (mfderiv (𝓡 3) (𝓡 3) Phi p v) =
      mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta c) p v at hv
  change mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (Phi p)
    (mfderiv (𝓡 3) (𝓡 3) Phi p w) =
      mfderiv (𝓡 3) (𝓡 3) (centeredNeckLift N theta c) p w at hw
  rw [hv, hw, hmap p hp]
  rw [source_initial_centered_tensor_evaluation _ theta c p L hL v w]
  simp only [surgeryCylinderPullback, dif_pos hs]
  rw [centeredCylinderLift_mfderiv, centeredCylinderLift_mfderiv,
    ← centeredNeckLift_mfderiv N theta c (hdomain hp),
    ← centeredNeckLift_mfderiv N theta c (hdomain hp)]
  rfl

end PoincareConjecture.M47
