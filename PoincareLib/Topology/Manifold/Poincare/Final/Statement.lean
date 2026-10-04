import PoincareLib.Topology.Manifold.Poincare.Final.Conclusion

/-!
# M90 final assembly statement

Natural-language theorem statement: a concrete M80 endpoint package yields a
final project package whose fields are exactly `SmoothPoincare` and
`TopologicalPoincare`. This fieldwise adapter is retained. The complete M90
assembly additionally constructs that package from actual milestones, with
no input service or endpoint premise. M83 supplies the initial topological
projective-plane exclusion in that checked producer.

Source: the primitive endpoint declarations in `PoincareMT.Statement`, the
M80 endpoint assembly contract, and the unified final-assembly requirement in
`GOAL-90-MILESTONE-REDESIGN.md`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

def M90FinalAssemblyStatement : Prop :=
  ∀ (_A : M80EndpointConclusion.{u}), Nonempty (M90FinalConclusion.{u})

/-- Both original endpoint propositions, produced without an input service. -/
def M90CompleteAssemblyStatement : Prop := Nonempty (M90FinalConclusion.{u})

end PoincareMT
