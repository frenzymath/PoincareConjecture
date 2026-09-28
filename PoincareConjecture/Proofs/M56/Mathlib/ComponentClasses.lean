import Mathlib.Topology.Connected.TotallyDisconnected








set_option autoImplicit false

namespace PoincareConjecture



theorem m56ComponentClass_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {x y : X}
    (h : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    ConnectedComponents.mk (f x) = ConnectedComponents.mk (f y) :=
  congrArg hf.connectedComponentsMap h

end PoincareConjecture
