import PoincareConjecture.Statements.M11GeneralizedFlow
import PoincareConjecture.Proofs.M11.CarrierAssembly
import PoincareConjecture.Proofs.M11.OrdinaryAssembly








set_option autoImplicit false

universe u

namespace PoincareConjecture



























theorem generalizedSpacetimeGeometry (n : ℕ) :
    GeneralizedSpacetimeGeometryTheory.{u} n := by
  constructor
  · intro X _ _ _ A
    exact ⟨Proofs.M11.adaptedCarrierConclusion A⟩
  · intro M _ _ _ _ _ _ g I hg
    exact ⟨Proofs.M11.ordinaryProductConclusion g I hg⟩

end PoincareConjecture
