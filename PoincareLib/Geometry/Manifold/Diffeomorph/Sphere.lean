import PoincareLib.Topology.Covering.SimplyConnected
import PoincareLib.Topology.Homotopy.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Compact local diffeomorphisms to spheres

For spheres of dimension at least two, a local diffeomorphism with compact
connected nonempty source is a diffeomorphism. This is the covering-space
step in the Gauss-map proof of Eschenburg's Lemma 6.6, pp. 517-518.
-/

noncomputable section
open scoped ContDiff Manifold

namespace Poincare.Geometry.Manifold

/-- A local diffeomorphism from a compact connected manifold to a standard
sphere of dimension at least two is a global diffeomorphism. -/
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
