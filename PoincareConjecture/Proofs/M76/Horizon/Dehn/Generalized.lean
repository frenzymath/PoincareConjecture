import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Annulus.Existence
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Disks.EnclosingRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.StandardProperDisk










set_option autoImplicit false

namespace PoincareConjecture.M76


theorem hasHamiltonProtectedDehnSurfaces : HasHamiltonProtectedDehnSurfaces := by
  constructor
  · intro L _ _ α e
    exact hasHamiltonProtectedDehnAnnulus L e
  · intro L _ _ α e
    exact hasHamiltonProtectedDehnDisks L e


theorem hasHamiltonGeneralizedDehnInput : HasHamiltonGeneralizedDehnInput :=
  ⟨hasHamiltonProtectedDehnSurfaces, hasHamiltonStandardProperDehnDisks⟩

end PoincareConjecture.M76
