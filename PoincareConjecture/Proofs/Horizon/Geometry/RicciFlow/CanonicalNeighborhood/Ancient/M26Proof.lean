import PoincareConjecture.Statements.M26CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Producer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Producer









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture



theorem horizon_m26CanonicalNeighborhoods
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} := by
  exact ⟨noncompactKappaSolutionAlternatives P, compactKappaSolutionAlternatives P⟩

theorem horizon_m26CanonicalNeighborhoodTheory
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    RepairedCanonicalNeighborhoodTheory.{u} :=
  horizon_m26CanonicalNeighborhoods P

end PoincareConjecture
