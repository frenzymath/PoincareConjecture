import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Stability.StableSliceChart
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Endpoint.EndpointDifferential
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Transport.BasisCoordinateVolume

/-!
# The actual stable endpoint chart in Euclidean source coordinates

Morgan-Tian Lemma 6.71, p. 141. The source coordinate equivalence preserves
the frozen source measure and converts the stable endpoint chart to the
Euclidean form needed for calibrated measure transport. Its derivative
is the actual endpoint tangent differential applied to the same coordinates.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

/-- The stable slice endpoint chart in a fixed source basis, for the
change-of-variables formula of Morgan-Tian Lemma 6.71, p. 141. -/
noncomputable def stableCoordinateChart (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (G.slices (T - τ)).Point :=
  b.euclideanCoordinates.toHomeomorph.transOpenPartialHomeomorph (stableSliceChart H)

/-- The coordinate chart source is exactly the preimage of the stable
carrier, Morgan-Tian Lemma 6.71, p. 141. -/
theorem stableCoordinateChart_source (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    (stableCoordinateChart H b).source = b.euclideanCoordinates ⁻¹' H.carrier := rfl

/-- The coordinate chart retains the exact stable endpoint image,
Morgan-Tian Lemma 6.71, p. 141. -/
theorem stableCoordinateChart_target (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) :
    (stableCoordinateChart H b).target = H.endpoint_slice_map '' H.carrier := rfl

/-- The forward coordinate map is the supplied slice endpoint map in the
specified source coordinates, Morgan-Tian Lemma 6.71, p. 141. -/
theorem stableCoordinateChart_apply (H : M14StableSet G T τ x E)
    (b : Module.Basis (Fin n) ℝ (G.Horizontal x)) (z : EuclideanSpace ℝ (Fin n)) :
    stableCoordinateChart H b z = H.endpoint_slice_map (b.euclideanCoordinates z) := rfl

/-- The Euclidean stable endpoint chart is smooth on its actual source,
Morgan-Tian Proposition 6.28 and Lemma 6.71, pp. 117, 141. -/
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

/-- The inverse coordinate chart is smooth on the actual stable image,
Morgan-Tian Proposition 6.28 and Lemma 6.71, pp. 117, 141. -/
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
-- Elaborating the dependent slice derivative unfolds the selected metric instances.
/-- The coordinate chart differential uses the same source basis and actual
endpoint tangent map as the metric Jacobian in Lemma 6.71, p. 141. -/
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

end PoincareMT.M14
