import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Component classes under continuous maps

Functoriality of the component quotient gives the elementary equality
calculation used in MT Definition 18.2, printed pp. 419--420.
-/

set_option autoImplicit false

namespace PoincareMT

/-- Continuous maps preserve equality of component classes, the basic
topological calculation for MT Definition 18.2, pp. 419--420. -/
theorem m56ComponentClass_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {x y : X}
    (h : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    ConnectedComponents.mk (f x) = ConnectedComponents.mk (f y) :=
  congrArg hf.connectedComponentsMap h

end PoincareMT
