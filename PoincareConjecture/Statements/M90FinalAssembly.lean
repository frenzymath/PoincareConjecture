import PoincareConjecture.Definitions.M90FinalAssembly
















set_option autoImplicit false

universe u

namespace PoincareConjecture

def M90FinalAssemblyStatement : Prop :=
  ∀ (_A : M80EndpointConclusion.{u}), Nonempty (M90FinalConclusion.{u})


def M90CompleteAssemblyStatement : Prop := Nonempty (M90FinalConclusion.{u})

end PoincareConjecture
