import PoincareConjecture.Proofs.M14.Sec6_3_StableSliceChart
import PoincareConjecture.Proofs.M14.Sec6_7_EndpointDifferential
import PoincareConjecture.Proofs.M14.Mathlib.BasisCoordinateVolume










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space



noncomputable def stableCoordinateChart (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (G.slices (T - τ)).Point :=
  b.euclideanCoordinates.toHomeomorph.transOpenPartialHomeomorph (stableSliceChart H)



theorem stableCoordinateChart_source (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    (stableCoordinateChart H b).source = b.euclideanCoordinates ⁻¹' H.carrier := rfl



theorem stableCoordinateChart_target (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    (stableCoordinateChart H b).target = H.endpoint_slice_map '' H.carrier := rfl



theorem stableCoordinateChart_apply (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) (z : EuclideanSpace ℝ (Fin n)) :
    stableCoordinateChart H b z = H.endpoint_slice_map (b.euclideanCoordinates z) := rfl



theorem stableCoordinateChart_smooth (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (stableCoordinateChart H b)
      (stableCoordinateChart H b).source := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hs : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞
      H.endpoint_slice_map H.carrier := H.endpoint_slice_smooth
  exact hs.comp b.euclideanCoordinates.toContinuousLinearMap.contMDiff.contMDiffOn
    (fun _ hz => hz)



theorem stableCoordinateChart_symm_smooth (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (stableCoordinateChart H b).symm
      (stableCoordinateChart H b).target := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hs : ContMDiffOn (𝓡 n) (𝓘(ℝ, G.Horizontal x)) ∞
      (stableSliceChart H).symm (stableSliceChart H).target :=
    stableSliceChart_symm_smooth H
  exact b.euclideanCoordinates.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn hs

set_option maxHeartbeats 800000 in



theorem stableCoordinateChart_differential (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (z : EuclideanSpace ℝ (Fin n))
    (hz : b.euclideanCoordinates z ∈ H.carrier) (v : EuclideanSpace ℝ (Fin n)) :
    mfderiv (𝓡 n) (𝓡 n) (stableCoordinateChart H b) z v =
      M14EndpointTangentDifferential G (b.euclideanCoordinates z) hz
        (b.euclideanCoordinates v) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let C := b.euclideanCoordinates
  have hs : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞
      H.endpoint_slice_map H.carrier := H.endpoint_slice_smooth
  have hf := (hs.contMDiffAt (H.carrier_open.mem_nhds hz)).mdifferentiableAt (by simp)
  rw [endpointTangentDifferential_eq_mfderiv]
  change mfderiv (𝓡 n) (𝓡 n) (H.endpoint_slice_map ∘ C) z v =
    mfderiv (𝓘(ℝ, G.Horizontal x)) (𝓡 n) H.endpoint_slice_map (C z) (C v)
  have hd := mfderiv_comp_apply z hf C.differentiableAt.mdifferentiableAt v
  rw [mfderiv_eq_fderiv, C.fderiv] at hd
  exact hd

end PoincareConjecture.M14
