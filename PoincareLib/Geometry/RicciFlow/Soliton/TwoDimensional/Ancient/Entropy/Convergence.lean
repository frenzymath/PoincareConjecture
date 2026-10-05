import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.Scalar
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Convergence.Volume

/-!
# Vanishing entropy of rescalings with a compact round limit

The frozen ancient convergence supplies uniform scalar convergence through
its metric jets and eventual global exhaustion diffeomorphisms. Gauss--Bonnet
then controls the areas, so the scale-invariant entropy tends to zero.

This supplies the backward-limit input for Hamilton's entropy argument
(Chow--Knopf, Proposition 5.39, p. 134), used in the two-dimensional ancient
classification (Morgan--Tian, Corollary 9.50, pp. 213--214).
-/

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 2 M} {S : AncientRescalingSequence K}

/-- Actual rescalings approaching a compact positive constant-curvature limit have vanishing entropy. -/
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

end PoincareMT.AncientCompactTimeConvergence
