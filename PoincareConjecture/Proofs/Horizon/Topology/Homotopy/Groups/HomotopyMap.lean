import Mathlib.Topology.Homotopy.HomotopyGroup








set_option autoImplicit false

open scoped Topology unitInterval

namespace Poincare.Topology


def mapGenLoop {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hxy : f x = y) (p : GenLoop N X x) :
    GenLoop N Y y :=
  ⟨f.comp p.val, fun u hu => (congrArg f (GenLoop.boundary p u hu)).trans hxy⟩


theorem mapGenLoop_homotopic {N X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hxy : f x = y) {p q : GenLoop N X x}
    (H : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f hxy p) (mapGenLoop f hxy q) := by
  exact ContinuousMap.HomotopicRel.comp_continuousMap H f


def homotopyGroupMap (N : Type*) {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hxy : f x = y) : HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map' (mapGenLoop f hxy) (fun _ _ h => mapGenLoop_homotopic f hxy h)


theorem homotopyGroupMap_mk {N X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hxy : f x = y) (p : GenLoop N X x) :
    homotopyGroupMap N f hxy ⟦p⟧ = ⟦mapGenLoop f hxy p⟧ := rfl

end Poincare.Topology
