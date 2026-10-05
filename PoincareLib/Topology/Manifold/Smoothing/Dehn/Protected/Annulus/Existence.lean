import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Descent.Tower.Original
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Protected.Annulus.Construction
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Protected.Annulus.EnclosingRegion

/-!
# The protected Dehn annulus from the original handle data

Finite circle surgery and marked tower descent construct the proper annulus.
Its retained-chart image and the bounded side of its capped sphere give the
unchanged protected annulus assertion. See Hamilton 1976, p. 67.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76

/-- The original protected index-one premises construct the annulus and its
enclosing region with both full boundary parametrizations. -/
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

end PoincareMT.M76
