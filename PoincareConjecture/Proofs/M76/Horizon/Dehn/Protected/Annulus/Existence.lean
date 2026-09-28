import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Tower.Original
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Annulus.Construction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Annulus.EnclosingRegion

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

theorem hasHamiltonProtectedDehnAnnulus
    (L : Submodule ℤ (Fin 2 → ℝ)) [DiscreteTopology L] {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 1) (Fin 2) L) (Fin 3 → ℝ)) :
    HasHamiltonProtectedDehnAnnulus L e := by
  intro he h hsource N hN hboundary hPL hretained
  obtain ⟨retained⟩ := hretained
  obtain ⟨k, hk, hki, hkin, hkb, hkfront⟩ :=
    Dehn.ProtectedAnnulus.exists_embedded_chart_annulus L retained he hsource hN hboundary hPL
  obtain ⟨T, _, _⟩ := Dehn.ProtectedAnnulus.exists_protected_annulus_of_chart
    L e he h retained k hk hki hkin hkb hkfront
  exact ⟨T, Dehn.ProtectedAnnulus.nonempty_enclosing_region
    L T he h hsource hboundary hPL retained⟩

end PoincareConjecture.M76
