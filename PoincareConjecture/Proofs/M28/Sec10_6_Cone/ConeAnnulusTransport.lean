import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SmoothBridge
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]





structure ConeAnnulusTransportData
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} where
  hab : a < b
  flow : RicciFlow 3 M (Icc a b)
  annulus : Set N
  annulus_compact : IsCompact annulus
  annulus_nonempty : annulus.Nonempty
  domain : Set N
  domain_open : IsOpen domain
  annulus_subset_domain : annulus ⊆ domain
  sourceMetric : RiemannianMetric 3 N
  sourceConnection : LeviCivitaData sourceMetric
  map : N → M
  map_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ map domain
  metric_isometry : ∀ y ∈ domain, ∀ u v : TangentSpace (𝓡 3) y,
    sourceMetric.inner y u v = (flow.metric b).inner (map y)
      (mfderiv (𝓡 3) (𝓡 3) map y u)
      (mfderiv (𝓡 3) (𝓡 3) map y v)
  sourcePoint : N
  sourcePoint_mem_annulus : sourcePoint ∈ annulus
  radial : TangentSpace (𝓡 3) sourcePoint
  radius : ℝ
  radius_pos : 0 < radius
  source_ricci_null :
    sourceConnection.ricci sourcePoint radial radial = 0
  source_scalar_pos : 0 < sourceConnection.scalarCurvature sourcePoint
  source_laplacian :
    sourceConnection.tensorLaplacian sourceConnection.ricciEvaluation
        sourcePoint ![radial, radial] =
      2 * sourceConnection.scalarCurvature sourcePoint / radius ^ 2
  operator_nonnegative : ∀ t ∈ Icc a b, ∀ x,
    (flow.connection t).NonnegativeCurvatureOperator x
  tensor_laplacian_transport :
    (flow.connection b).tensorLaplacian (flow.connection b).ricciEvaluation
        (map sourcePoint)
        ![mfderiv (𝓡 3) (𝓡 3) map sourcePoint radial,
          mfderiv (𝓡 3) (𝓡 3) map sourcePoint radial] =
      sourceConnection.tensorLaplacian sourceConnection.ricciEvaluation
        sourcePoint ![radial, radial]

noncomputable def ConeAnnulusTransportData.to_smooth_cone_obstruction
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ}
    (C : ConeAnnulusTransportData (M := M) (N := N) P (a := a) (b := b)) :
    SmoothConeObstructionData (M := M) P (a := a) (b := b) := by
  have hpoint_domain : C.sourcePoint ∈ C.domain :=
    C.annulus_subset_domain C.sourcePoint_mem_annulus
  have hscalar := C.sourceConnection.scalarCurvature_eq_of_local_isometry
    (C.flow.connection b)
    C.domain_open C.map_smooth C.metric_isometry hpoint_domain
  have hricci := C.sourceConnection.ricci_eq_of_local_isometry
    (C.flow.connection b)
    C.domain_open C.map_smooth C.metric_isometry hpoint_domain
    C.radial C.radial
  refine
    { hab := C.hab
      flow := C.flow
      operator_nonnegative := C.operator_nonnegative
      point := C.map C.sourcePoint
      radial := mfderiv (𝓡 3) (𝓡 3) C.map C.sourcePoint C.radial
      radial_ricci_null := ?_
      radius := C.radius
      radius_pos := C.radius_pos
      scalar_pos := ?_
      radial_laplacian := ?_ }
  · simpa only using (hricci.symm.trans C.source_ricci_null)
  · rw [← hscalar]
    exact C.source_scalar_pos
  · calc
      (C.flow.connection b).tensorLaplacian
          (C.flow.connection b).ricciEvaluation (C.map C.sourcePoint)
          ![mfderiv (𝓡 3) (𝓡 3) C.map C.sourcePoint C.radial,
            mfderiv (𝓡 3) (𝓡 3) C.map C.sourcePoint C.radial] =
        C.sourceConnection.tensorLaplacian C.sourceConnection.ricciEvaluation
          C.sourcePoint ![C.radial, C.radial] :=
        C.tensor_laplacian_transport
      _ = 2 * C.sourceConnection.scalarCurvature C.sourcePoint / C.radius ^ 2 :=
        C.source_laplacian
      _ = 2 * (C.flow.connection b).scalarCurvature (C.map C.sourcePoint) /
          C.radius ^ 2 := by rw [hscalar]

end PoincareConjecture.M28
