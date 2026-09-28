import PoincareConjecture.Statements.M57Transport
import PoincareConjecture.Proofs.M57.Adapters
import PoincareConjecture.Proofs.M57.Sec18_Prop18_18.AncestryInput

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedAncestryTransport : RepairedTransportTheory.{u} := by
  refine { poincare_inputs := ?_, transport := ?_ }
  · exact m57PoincareAncestryInput
  · intro B G40 g₀ D W A K C hC T hT x H
    exact m57AncestryTransport_of_input D W (A.path_for T hT x) K C H B

end PoincareConjecture
