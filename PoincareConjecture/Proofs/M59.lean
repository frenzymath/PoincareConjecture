import PoincareConjecture.Proofs.M59.Providers
import PoincareConjecture.Proofs.M59.Sec4_1_Whiskering.Service
import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.IdentificationSystem

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m59LoopClassesAndComponentTopology
    (P02 : RepairedClosedTopologyProvider.{u})
    (P58 : RepairedShortLoopTrivialityTheory.{u}) :
    M59LoopClassesAndComponentTopologyTheory.{u} := by
  let S := m59IdentificationSystem P02
  refine ⟨S, m59ComponentRepresentative_from_identification S, ?_⟩
  exact ⟨m59ShortLoopPiThree_of_service P58 S, m59HigherBasepointTransportService_nonempty⟩

theorem m59LoopClassesAndComponentTopology_from_predecessors :
    M59LoopClassesAndComponentTopologyTheory.{u} :=
  m59LoopClassesAndComponentTopology m59ClosedTopologyProvider_from_M02
    repairedShortLoopTriviality

end PoincareConjecture
