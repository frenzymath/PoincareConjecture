import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Based postcomposition on homotopy classes

Continuous postcomposition preserves the cube boundary condition and homotopy
relative to that boundary, and therefore acts on the actual quotient.
-/

set_option autoImplicit false

open scoped Topology unitInterval

namespace Poincare.Topology

/-- Postcompose a based cube by a map carrying its basepoint to the given point. -/
def mapGenLoop {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hxy : f x = y) (p : GenLoop N X x) :
    GenLoop N Y y :=
  ⟨f.comp p.val, fun u hu => (congrArg f (GenLoop.boundary p u hu)).trans hxy⟩

/-- Postcomposition preserves the relation defining the homotopy quotient. -/
theorem mapGenLoop_homotopic {N X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hxy : f x = y) {p q : GenLoop N X x}
    (H : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (mapGenLoop f hxy p) (mapGenLoop f hxy q) := by
  exact ContinuousMap.HomotopicRel.comp_continuousMap H f

/-- The quotient map induced by based continuous postcomposition. -/
def homotopyGroupMap (N : Type*) {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hxy : f x = y) : HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map' (mapGenLoop f hxy) (fun _ _ h => mapGenLoop_homotopic f hxy h)

/-- The induced map sends a cube class to its postcomposition class. -/
theorem homotopyGroupMap_mk {N X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hxy : f x = y) (p : GenLoop N X x) :
    homotopyGroupMap N f hxy ⟦p⟧ = ⟦mapGenLoop f hxy p⟧ := rfl

end Poincare.Topology
