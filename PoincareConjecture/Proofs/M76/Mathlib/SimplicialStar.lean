import Mathlib.Analysis.Convex.SimplicialComplex.Basic

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]

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

theorem finite_closedStar_faces {K : SimplicialComplex 𝕜 E} (hK : K.faces.Finite) (p : E) :
    (K.closedStar p).faces.Finite := hK.subset (fun _ hs => hs.1)

theorem finite_link_faces {K : SimplicialComplex 𝕜 E} (hK : K.faces.Finite) (p : E) :
    (K.link p).faces.Finite := hK.subset (fun _ hs => hs.1)

theorem link_le_closedStar (K : SimplicialComplex 𝕜 E) (p : E) :
    K.link p ≤ K.closedStar p := fun _ hs => ⟨hs.1, hs.2.2⟩

end Geometry.SimplicialComplex
