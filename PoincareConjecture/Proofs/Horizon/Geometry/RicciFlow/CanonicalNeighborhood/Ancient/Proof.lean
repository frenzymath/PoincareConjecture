import PoincareConjecture.Statements.M27KappaAlternatives
import PoincareConjecture.Statements.M27Providers
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Producer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Producer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactAssembly
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactCoverage.Alternatives









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture


theorem horizon_m27KappaAlternatives
    (P : M27KappaAlternativePredecessors.{u}) :
    RepairedKappaAlternativeTheory.{u} := by
  exact m27KappaAlternatives_of_compact_classification P (compact_positive_classification_of_m27 P)

end PoincareConjecture
