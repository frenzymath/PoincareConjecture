import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonRegions

/-!
# Propagating polygon region membership across connected sets

A preconnected set avoiding the boundary belongs to the same
canonical region as any one of its points. This supports the
corner-cap inside classification for the diagonal lemma in
Erickson, pp. 7--8. See M76 derivation 106.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- A preconnected set avoiding a polygon boundary and meeting
its inside is contained in the inside. Simplicity is not needed.
See M76 derivation 106. -/
theorem subset_inside_of_preconnected_inter (P : Polygon E n) {S : Set E}
    (hS : IsPreconnected S) (hsub : S ⊆ (P.boundary ℝ)ᶜ)
    (hinter : (S ∩ P.inside).Nonempty) : S ⊆ P.inside := by
  obtain ⟨x, hxS, hxi⟩ := hinter
  intro y hy
  refine ⟨hsub hy, ?_⟩
  have heq := connectedComponentIn_eq (hS.subset_connectedComponentIn hxS hsub hy)
  rw [← heq]
  exact hxi.2

/-- A preconnected set avoiding a polygon boundary and meeting
its outside is contained in the outside. Simplicity is not needed.
See M76 derivation 106. -/
theorem subset_outside_of_preconnected_inter (P : Polygon E n) {S : Set E}
    (hS : IsPreconnected S) (hsub : S ⊆ (P.boundary ℝ)ᶜ)
    (hinter : (S ∩ P.outside).Nonempty) : S ⊆ P.outside := by
  obtain ⟨x, hxS, hxo⟩ := hinter
  intro y hy
  refine ⟨hsub hy, ?_⟩
  have heq := connectedComponentIn_eq (hS.subset_connectedComponentIn hxS hsub hy)
  rw [← heq]
  exact hxo.2

end Polygon
