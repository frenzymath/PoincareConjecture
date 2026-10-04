import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Basepoint.GenLoopWhisker

/-!
# The uniform higher basepoint service

The moving-boundary construction commutes with continuous postcomposition.
It supplies M59's service for every space and dimension, using exactly the
frozen surgery homotopy map. Source: Hatcher, Section 4.1, pp. 341-342.
-/

set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

universe u

namespace PoincareMT

/-- The constructed higher basepoint service, including continuous naturality.
Source: Hatcher, Section 4.1, pp. 341-342. -/
def m59HigherBasepointTransportService : M59HigherBasepointTransportService.{u} where
  transport n {X} _ := m59HigherBasepointTransport X n
  naturality := by
    intro n X Y _ _ f x y p a
    refine Quotient.inductionOn a ?_
    intro a
    exact Quotient.sound (GenLoop.boundaryTransport_map p a f)

/-- M59's basepoint service exists without any manifold or predecessor hypothesis.
Source: Hatcher, Section 4.1, pp. 341-342. -/
theorem m59HigherBasepointTransportService_nonempty :
    Nonempty M59HigherBasepointTransportService.{u} :=
  ⟨m59HigherBasepointTransportService⟩

end PoincareMT
