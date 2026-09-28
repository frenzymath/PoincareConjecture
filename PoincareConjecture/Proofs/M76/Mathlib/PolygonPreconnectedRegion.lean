import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegions

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

theorem subset_inside_of_preconnected_inter (P : Polygon E n) {S : Set E}
    (hS : IsPreconnected S) (hsub : S ⊆ (P.boundary ℝ)ᶜ)
    (hinter : (S ∩ P.inside).Nonempty) : S ⊆ P.inside := by
  obtain ⟨x, hxS, hxi⟩ := hinter
  intro y hy
  refine ⟨hsub hy, ?_⟩
  have heq := connectedComponentIn_eq (hS.subset_connectedComponentIn hxS hsub hy)
  rw [← heq]
  exact hxi.2

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
