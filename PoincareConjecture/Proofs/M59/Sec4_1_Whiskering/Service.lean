import PoincareConjecture.Proofs.M59.Sec4_1_Whiskering.GenLoopWhisker









set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

universe u

namespace PoincareConjecture



def m59HigherBasepointTransportService : M59HigherBasepointTransportService.{u} where
  transport n {X} _ := m59HigherBasepointTransport X n
  naturality := by
    intro n X Y _ _ f x y p a
    refine Quotient.inductionOn a ?_
    intro a
    exact Quotient.sound (GenLoop.boundaryTransport_map p a f)



theorem m59HigherBasepointTransportService_nonempty :
    Nonempty M59HigherBasepointTransportService.{u} :=
  ⟨m59HigherBasepointTransportService⟩

end PoincareConjecture
