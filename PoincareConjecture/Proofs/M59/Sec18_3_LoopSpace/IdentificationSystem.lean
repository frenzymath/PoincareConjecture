import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.CompactDeckFromComparison
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.OrderComplexLiftComparison

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m59CompactCoverDeckAction (P02 : RepairedClosedTopologyProvider.{u}) :
    M59CompactCoverDeckAction.{u} :=
  m59CompactCoverDeckAction_of_orderComplexComparison P02
    (fun _ _ _ _ _ p hp => Proofs.M59.orderComplexSingularLift_quasiIso p hp)

noncomputable def m59IdentificationSystem (P02 : RepairedClosedTopologyProvider.{u}) :
    M59IdentificationSystem.{u} :=
  m59IdentificationSystem_of_compact_cover_deck (m59CompactCoverDeckAction P02)

end PoincareConjecture
