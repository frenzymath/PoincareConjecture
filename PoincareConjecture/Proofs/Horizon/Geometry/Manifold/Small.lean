import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Transport
import PoincareConjecture.Proofs.Horizon.Topology.SecondCountable.Small









open scoped Manifold ContDiff

universe u

namespace Poincare.Manifold


@[instance_reducible]
noncomputable def shrinkChartedSpace (H : Type*) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [T0Space M] [SecondCountableTopology M]
    [ChartedSpace H M] :
    letI : Small.{0} M := Poincare.Topology.SecondCountable.small M
    ChartedSpace H (Shrink.{0} M) := by
  letI : Small.{0} M := Poincare.Topology.SecondCountable.small M
  exact HomeomorphTransport.chartedSpace (H := H)
    (Poincare.Topology.SecondCountable.homeomorphShrink M)

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  (M : Type u) [TopologicalSpace M] [T0Space M] [SecondCountableTopology M]
  [ChartedSpace H M] [IsManifold I ∞ M]


theorem shrinkIsManifold :
    letI : Small.{0} M := Poincare.Topology.SecondCountable.small M
    letI := shrinkChartedSpace H M
    IsManifold I ∞ (Shrink.{0} M) := by
  let : Small.{0} M := Poincare.Topology.SecondCountable.small M
  let := shrinkChartedSpace H M
  exact HomeomorphTransport.isManifold
    (Poincare.Topology.SecondCountable.homeomorphShrink M) I ∞


noncomputable def shrinkDiffeomorph :
    letI : Small.{0} M := Poincare.Topology.SecondCountable.small M
    letI := shrinkChartedSpace H M
    Diffeomorph I I M (Shrink.{0} M) ∞ := by
  letI : Small.{0} M := Poincare.Topology.SecondCountable.small M
  letI := shrinkChartedSpace H M
  exact HomeomorphTransport.diffeomorph
    (Poincare.Topology.SecondCountable.homeomorphShrink M) I ∞


theorem shrinkDiffeomorph_toEquiv :
    letI : Small.{0} M := Poincare.Topology.SecondCountable.small M
    letI := shrinkChartedSpace H M
    (shrinkDiffeomorph I M).toEquiv = equivShrink M := rfl

end Poincare.Manifold
