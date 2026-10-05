import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# Closed stars and links in geometric simplicial complexes

The closed star of a vertex consists of the faces that can be joined to
that vertex; the link removes the vertex. These are the stars used by
Cairns 1940, Sections 4--6, pp. 800--802. See M76 derivation 16.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

/-- The closed star contains exactly the faces that can be joined to
the specified vertex. See Cairns pp. 800--802 and M76 derivation 16. -/
def closedStar (K : SimplicialComplex 𝕜 E) (p : E) : SimplicialComplex 𝕜 E where
  faces := {s | s ∈ K.faces ∧ insert p s ∈ K.faces}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht,
      K.down_closed hs.2 (Finset.insert_subset_insert p hts) (Finset.insert_nonempty p t)⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

/-- The link contains the closed-star faces omitting its vertex.
See Cairns pp. 800--802 and M76 derivation 16. -/
def link (K : SimplicialComplex 𝕜 E) (p : E) : SimplicialComplex 𝕜 E where
  faces := {s | s ∈ K.faces ∧ p ∉ s ∧ insert p s ∈ K.faces}
  indep hs := K.indep hs.1
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, fun hp => hs.2.1 (hts hp),
      K.down_closed hs.2.2 (Finset.insert_subset_insert p hts) (Finset.insert_nonempty p t)⟩
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

/-- Taking a closed star preserves finiteness. See M76 derivation 16. -/
theorem finite_closedStar_faces {K : SimplicialComplex 𝕜 E} (hK : K.faces.Finite) (p : E) :
    (K.closedStar p).faces.Finite := hK.subset (fun _ hs => hs.1)

/-- Taking a link preserves finiteness. See M76 derivation 16. -/
theorem finite_link_faces {K : SimplicialComplex 𝕜 E} (hK : K.faces.Finite) (p : E) :
    (K.link p).faces.Finite := hK.subset (fun _ hs => hs.1)

/-- Every link face belongs to the closed star. See M76 derivation 16. -/
theorem link_le_closedStar (K : SimplicialComplex 𝕜 E) (p : E) :
    K.link p ≤ K.closedStar p := fun _ hs => ⟨hs.1, hs.2.2⟩

end Geometry.SimplicialComplex
