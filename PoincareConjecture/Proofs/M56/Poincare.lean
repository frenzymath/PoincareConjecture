import PoincareConjecture.Proofs.M54
import PoincareConjecture.Proofs.M55
import PoincareConjecture.Proofs.M56
import PoincareConjecture.Proofs.M52.Assembly











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M]
  {N : NormalizedInitialMetric (M := M)}




theorem m56PoincareAncestryFromTheories
    (G56 : RepairedAncestryTheory.{u})
    (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow) :
    Nonempty {P : M56PoincareAncestryData (m52CoreFlowData G).flow L //
      M56PoincareProviderRealization G54 G55 P} :=
  G56.poincare G54 G55 N G L





theorem m56PoincareAncestryFromMilestones
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow) :
    Nonempty (M56PoincareAncestryData (m52CoreFlowData G).flow L) := by
  obtain ⟨P, _hP⟩ := m56PoincareAncestryFromTheories
    repairedFiniteAncestry repairedGroupEffects repairedChildComponents G L
  exact ⟨P⟩

end PoincareConjecture
