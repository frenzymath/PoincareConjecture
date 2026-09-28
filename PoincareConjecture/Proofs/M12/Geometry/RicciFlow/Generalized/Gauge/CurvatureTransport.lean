import PoincareConjecture.Proofs.M12.Geometry.Spacetime.SliceTransport
import PoincareConjecture.Proofs.M12.Geometry.RicciFlow.Generalized.Gauge.SliceGeometry
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {S : ∀ s : ℝ, SpacetimeSliceGeometry F s}
  {T : SmoothSpacetimeInterval K} {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {e : MovingSpacetimeGauge F T C}

structure MovingGaugeCurvatureTransportFields
    (D : LeafwiseLeviCivitaFamily F S)
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric) : Prop where
  riemann_eq : ∀ (t : T.Point) (x : C)
      (u v w z : TangentSpace (𝓡 n) x),
    (c t.val).curvatureTensor x u v w z =
      horizontalRiemann D (e.toSpacetime (t, x))
        (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)
        (G.spatialTangentEquiv t x w) (G.spatialTangentEquiv t x z)
  ricci_eq : ∀ (t : T.Point) (x : C)
      (u v : TangentSpace (𝓡 n) x),
    (c t.val).ricci x u v = horizontalRicci D (e.toSpacetime (t, x))
      (G.spatialTangentEquiv t x u) (G.spatialTangentEquiv t x v)
  scalar_eq : ∀ (t : T.Point) (x : C),
    (c t.val).scalarCurvature x =
      horizontalScalarCurvature D (e.toSpacetime (t, x))
  curvature_norm_eq : ∀ (t : T.Point) (x : C),
    (c t.val).curvatureTensorNorm x =
      horizontalCurvatureNorm D (e.toSpacetime (t, x))

private theorem slice_deriv_eq_tangent_symm
    (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e)
    (t : T.Point) (x : C) (u : TangentSpace (𝓡 n) x) :
    ((S t.val).tangentEquiv (movingGaugeSliceMap e S t x)).symm
        (G.spatialTangentEquiv t x u) =
      mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) x u := by
  rw [← movingGaugeSliceMap_tangent_eq e S G t x u]
  exact (S t.val).tangentEquiv (movingGaugeSliceMap e S t x)
    |>.symm_apply_apply _

theorem movingGaugeCurvatureTransportFields
    (D : LeafwiseLeviCivitaFamily F S)
    (e : MovingSpacetimeGauge F T C)
    (G : MovingSpacetimeGaugeGeometry e)
    (c : MetricLeviCivitaFamily G.metric) :
    MovingGaugeCurvatureTransportFields D G c := by
  have hmetric (t : T.Point) : ∀ y ∈ (Set.univ : Set C),
      ∀ a b : TangentSpace (𝓡 n) y,
      (G.metric t.val).inner y a b =
        (S t.val).metricOnPoints.inner (movingGaugeSliceMap e S t y)
          (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) y a)
          (mfderiv (𝓡 n) (𝓡 n) (movingGaugeSliceMap e S t) y b) := by
    intro y _ a b
    exact ((movingGaugeSliceGeometryFields (S := S) e G).slice_metric_eq t y a b).symm
  refine { riemann_eq := ?_, ricci_eq := ?_, scalar_eq := ?_, curvature_norm_eq := ?_ }
  · intro t x u v w z
    have hlocal := movingGaugeSliceMap_localDiffeomorph e S G t
    have h := (c t.val).curvatureTensor_eq_of_local_isometry (D.sliceConnection t.val)
      isOpen_univ hlocal.contMDiff.contMDiffOn (hmetric t) (mem_univ x) u v w z
    rw [← slice_deriv_eq_tangent_symm e G t x u,
      ← slice_deriv_eq_tangent_symm e G t x v,
      ← slice_deriv_eq_tangent_symm e G t x w,
      ← slice_deriv_eq_tangent_symm e G t x z] at h
    rw [horizontalRiemann_eq_slice D _ (e.time_eq (t, x))]
    exact h
  · intro t x u v
    have hlocal := movingGaugeSliceMap_localDiffeomorph e S G t
    have h := (c t.val).ricci_eq_of_local_isometry (D.sliceConnection t.val)
      isOpen_univ hlocal.contMDiff.contMDiffOn (hmetric t) (mem_univ x) u v
    rw [← slice_deriv_eq_tangent_symm e G t x u,
      ← slice_deriv_eq_tangent_symm e G t x v] at h
    rw [horizontalRicci_eq_slice D _ (e.time_eq (t, x))]
    exact h
  · intro t x
    have hlocal := movingGaugeSliceMap_localDiffeomorph e S G t
    have h := (c t.val).scalarCurvature_eq_of_local_isometry
      (D.sliceConnection t.val) isOpen_univ hlocal.contMDiff.contMDiffOn
      (hmetric t) (mem_univ x)
    rw [horizontalScalarCurvature_eq_slice D _ (e.time_eq (t, x))]
    exact h
  · intro t x
    have hlocal := movingGaugeSliceMap_localDiffeomorph e S G t
    have h := (c t.val).curvatureTensorNorm_eq_of_local_isometry
      (D.sliceConnection t.val) isOpen_univ hlocal.contMDiff.contMDiffOn
      (hmetric t) (mem_univ x)
    rw [horizontalCurvatureNorm_eq_slice D _ (e.time_eq (t, x))]
    exact h

end PoincareConjecture
