import PoincareLib.Topology.Manifold.Smoothing.Dehn.Protected.Annulus.Existence
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Protected.Disks.EnclosingRegion
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.StandardProperDisk

/-!
# Hamilton's generalized Dehn input

The protected index-one and index-two constructions and the standard proper
disk theorem discharge the original generalized Dehn predicate, preserving
all marked boundary maps and the complete domain frontier. See Hamilton 1976,
p. 67, and the preserved M76 derivations 320, 337 and 338.
-/

set_option autoImplicit false

namespace PoincareMT.M76

/-- Both protected handle cases, with their original lattice and atlas quantifiers. -/
theorem hasHamiltonProtectedDehnSurfaces : HasHamiltonProtectedDehnSurfaces := by
  constructor
  · intro L _ _ α e
    exact hasHamiltonProtectedDehnAnnulus L e
  · intro L _ _ α e
    exact hasHamiltonProtectedDehnDisks L e

/-- The unchanged generalized Dehn input is constructed without additional suppliers. -/
theorem hasHamiltonGeneralizedDehnInput : HasHamiltonGeneralizedDehnInput :=
  ⟨hasHamiltonProtectedDehnSurfaces, hasHamiltonStandardProperDehnDisks⟩

end PoincareMT.M76
