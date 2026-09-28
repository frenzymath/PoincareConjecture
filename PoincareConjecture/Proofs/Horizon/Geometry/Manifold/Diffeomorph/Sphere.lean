import PoincareConjecture.Proofs.Horizon.Topology.Covering.SimplyConnected
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph









noncomputable section
open scoped ContDiff Manifold

namespace Poincare.Geometry.Manifold



def sphereDiffeomorphOfLocalDiffeomorph
    {n : ℕ} {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 2))) S]
    [CompactSpace S] [ConnectedSpace S]
    (f : S → Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 2) + 1))) 1)
    (hf : IsLocalDiffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) ∞ f) :
    Diffeomorph (𝓡 (n + 2)) (𝓡 (n + 2)) S
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 2) + 1))) 1) ∞ := by
  let : SimplyConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 2) + 1))) 1) :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (by omega)
  let : LocallyPathConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin ((n + 2) + 1))) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 2))) _
  exact hf.diffeomorphOfBijective
    (Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected
      (isLocalHomeomorph_iff_isCoveringMap.mp hf.isLocalHomeomorph))

end Poincare.Geometry.Manifold
