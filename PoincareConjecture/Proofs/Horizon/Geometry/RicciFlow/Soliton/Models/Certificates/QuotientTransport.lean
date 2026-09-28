import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Refined
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.ProjectivePlane
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_quotientFlowTransport
    {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}
    (q : QuotientSphereLineCertificate G) : Nonempty (M24QuotientFlowTransport q) := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.product_charted
  let := q.product.product_manifold
  let := q.quotient_topology
  let := q.quotient_charted
  let := q.quotient_manifold
  obtain ⟨e, he⟩ := q.flow_isometric_to_quotient
  refine ⟨{
    quotient_map_local_diffeomorph := q.quotient_map_localDiffeomorph
    flow_identification := e
    flow_metric_transport := he
    product_curvature_transport := ?_
    flow_curvature_transport := ?_ }⟩
  · intro t ht x v w
    unfold LeviCivitaData.sectionalCurvature
    rw [(q.product.product_connection t).curvatureTensor_eq_of_local_isometry
      (q.quotient_connection t) isOpen_univ q.quotient_map_smooth.contMDiffOn
      (fun y _ a b => q.quotient_metric_pullback t ht y a b) (mem_univ x)]
    rw [q.quotient_metric_pullback t ht x v v,
      q.quotient_metric_pullback t ht x w w, q.quotient_metric_pullback t ht x v w]
  · intro t ht x v w
    unfold LeviCivitaData.sectionalCurvature
    rw [(G.flow.connection t).curvatureTensor_eq_of_local_isometry
      (q.quotient_connection t) isOpen_univ e.contMDiff.contMDiffOn
      (fun y _ a b => he t ht y a b) (mem_univ x)]
    rw [he t ht x v v, he t ht x w w, he t ht x v w]

end PoincareConjecture
