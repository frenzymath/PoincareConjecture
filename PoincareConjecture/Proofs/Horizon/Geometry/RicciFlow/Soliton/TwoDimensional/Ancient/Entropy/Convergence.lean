import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.Volume

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 2 M} {S : AncientRescalingSequence K}

theorem tendsto_scalarEntropy_rescaling
    (G : AncientCompactTimeConvergence S) (hcompact : CompactSpace G.limit.carrier.carrier)
    {c : ℝ} (hc : 0 < c)
    (hround : ∀ x, (G.limit.flow.connection (-1)).scalarCurvature x = c) :
    Tendsto (fun k => SurfaceEntropy.scalarEntropy
      ((S.rescaling (G.subsequence k)).flow.connection (-1))) atTop (𝓝 0) := by
  let : CompactSpace M := G.compactSpace_of_compact_limit hcompact
  have hR := G.tendstoUniformly_scalarCurvature_rescaling_neg_one hcompact hround
  exact SurfaceEntropy.tendsto_scalarEntropy_of_uniform_scalar
    (fun k => (S.rescaling (G.subsequence k)).flow.connection (-1)) hc hR
    (SurfaceEntropy.eventually_volume_le_of_uniform_scalar _ hc hR)

end PoincareConjecture.AncientCompactTimeConvergence
