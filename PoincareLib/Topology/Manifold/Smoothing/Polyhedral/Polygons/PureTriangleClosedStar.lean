import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplicialStar

/-!
# Covering a closed vertex star by original triangles

In a pure triangle complex, every closed-star face extends
together with the distinguished vertex to an original triangle.
See Alexander 1924, pp. 6--8 and M76 derivation 217.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [DecidableEq E]

/-- The closed star in a pure triangle complex is exactly
covered by original triangles containing its vertex, including
all their lower-dimensional faces. See M76 derivation 217. -/
theorem mem_closedStar_space_iff_triangle (K : SimplicialComplex 𝕜 E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) (q x : E) :
    x ∈ (K.closedStar q).space ↔
      ∃ s ∈ K.faces, s.card = 3 ∧ q ∈ s ∧ x ∈ convexHull 𝕜 (s : Set E) := by
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, htc, hst⟩ := hpure (insert q s) hs.2
    exact ⟨t, ht, htc, hst (Finset.mem_insert_self _ _),
      convexHull_mono ((Finset.subset_insert q s).trans hst) hxs⟩
  · rintro ⟨s, hs, _, hqs, hxs⟩
    exact mem_space_iff.mpr ⟨s, ⟨hs, by simpa only [Finset.insert_eq_of_mem hqs] using hs⟩, hxs⟩

/-- The actual link in a pure triangle complex is the union
of the opposite faces of original triangles through its
vertex. See Alexander pp. 6--8 and M76 derivation 223. -/
theorem mem_link_space_iff_triangle (K : SimplicialComplex 𝕜 E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) (q x : E) :
    x ∈ (K.link q).space ↔
      ∃ s ∈ K.faces, s.card = 3 ∧ q ∈ s ∧
        x ∈ convexHull 𝕜 ((s : Set E) \ {q}) := by
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, htc, hst⟩ := hpure (insert q s) hs.2.2
    refine ⟨t, ht, htc, hst (Finset.mem_insert_self _ _), convexHull_mono ?_ hxs⟩
    intro y hy
    exact ⟨hst (Finset.mem_insert_of_mem hy), fun hyq => hs.2.1 (hyq ▸ hy)⟩
  · rintro ⟨s, hs, hsc, hqs, hxs⟩
    have hcard : (s.erase q).card = 2 := by rw [Finset.card_erase_of_mem hqs, hsc]
    have hne : (s.erase q).Nonempty := Finset.card_pos.mp (by omega)
    refine mem_space_iff.mpr ⟨s.erase q, ?_, ?_⟩
    · exact ⟨K.down_closed hs (Finset.erase_subset _ _) hne, Finset.notMem_erase _ _,
        by simpa only [Finset.insert_erase hqs] using hs⟩
    · simpa only [Finset.coe_erase] using hxs

end Geometry.SimplicialComplex
