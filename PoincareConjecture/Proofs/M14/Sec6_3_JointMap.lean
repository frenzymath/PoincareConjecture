import PoincareConjecture.Proofs.M14.Sec6_3_JointInverse
import PoincareConjecture.Proofs.M14.Sec6_3_JointBranches
import PoincareConjecture.Proofs.M14.Sec6_7_MetricBases
import PoincareConjecture.Proofs.M14.Mathlib.BasisCoordinateVolume
import PoincareConjecture.Statements.M14Exponential










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space




noncomputable def jointMapData (E : M14ExponentialFamily G T x) : M14JointMapData G T x E := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let b := (exists_orthonormal_horizontalBasis G x).choose
  let D := range (fun z : M14JointDomain G E => E.gamma z.1.1 z.1.2)
  have hsm : ContMDiffOn (spacetimeModel n) (𝓘(ℝ, G.Horizontal x × ℝ)) ∞
      (jointEndpointInverse E) D := jointEndpointInverse_smooth E
  refine {
    image := D
    image_eq := rfl
    injective := (jointMap_injective E).injOn
    image_relative_open := ⟨D, jointMap_range_isOpen E, rfl⟩
    map_continuous := jointMap_continuous E
    map_open := jointMap_isOpenMap E
    inverse := jointEndpointInverse E
    inverse_mem := fun _ hq => (jointEndpointInverse_spec E hq).1
    inverse_on_image := fun _ hq => (jointEndpointInverse_spec E hq).2
    inverse_left := jointEndpointInverse_left E
    inverse_continuous := jointEndpointInverse_continuous E
    coordinate_basis := b
    inverse_vector_smooth := ?_
    inverse_time_smooth := ?_
    differential_bijective := ?_
    time_component := jointMap_clock E
    action_branch := fun z => jointDomain_action_branch E z.property }
  · let A : (G.Horizontal x × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
      b.euclideanCoordinates.symm.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ _ ℝ)
    exact A.contMDiff.comp_contMDiffOn hsm
  · exact (ContinuousLinearMap.snd ℝ (G.Horizontal x) ℝ).contMDiff.comp_contMDiffOn hsm
  · intro z
    obtain ⟨H, hZ⟩ := jointDomain_stableSet E z.property
    exact ⟨H, hZ, H.endpoint_differential_bijective z.1.1 hZ⟩



theorem jointMapData_nonempty (E : M14ExponentialFamily G T x) :
    Nonempty (M14JointMapData G T x E) := ⟨jointMapData E⟩

end PoincareConjecture.M14
