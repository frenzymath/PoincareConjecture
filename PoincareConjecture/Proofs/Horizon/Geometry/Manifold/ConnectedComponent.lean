import Mathlib.Geometry.Manifold.ChartedSpace



set_option autoImplicit false

namespace Poincare

variable (H : Type*) [TopologicalSpace H] [LocallyConnectedSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


def connectedComponentOpens (p : M) : TopologicalSpace.Opens M := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  exact ⟨connectedComponent p, isOpen_connectedComponent⟩

@[simp] theorem coe_connectedComponentOpens (p : M) :
    (connectedComponentOpens H p : Set M) = connectedComponent p := rfl

instance connectedComponentOpens_connectedSpace (p : M) :
    ConnectedSpace (connectedComponentOpens H p) :=
  Subtype.connectedSpace isConnected_connectedComponent

end Poincare
