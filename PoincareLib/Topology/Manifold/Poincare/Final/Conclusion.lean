import PoincareLib.Topology.Manifold.Poincare.Assembly.Conclusion

/-!
# M90 final endpoint assembly

M90 is the named final adapter from the reviewed M80 package to the two
primitive endpoint propositions used by the project theorem.  It introduces
no new mathematical premise.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

structure M90FinalConclusion where
  smooth : SmoothPoincare.{u}
  topological : TopologicalPoincare.{u}

end PoincareMT
