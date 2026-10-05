import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!+# Directed unions of geometric complexes

Directed unions preserve the affine independence and geometric
intersection law because every pair of faces lies in one upper
member. See Hudson 1969, pp. 3--5 and M76 derivation 84.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {ι 𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- The union of a directed family of geometric subcomplexes.
See Hudson pp. 3--5 and M76 derivation 84. -/
def directedUnion (K : ι → SimplicialComplex 𝕜 E) (hK : Directed (· ≤ ·) K) :
    SimplicialComplex 𝕜 E where
  faces := ⋃ i, (K i).faces
  indep := by
    rintro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact (K i).indep hi
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    refine ⟨(K i).nonempty_of_mem_faces hi, fun t hts ht => ?_⟩
    exact mem_iUnion.mpr ⟨i, (K i).down_closed hi hts ht⟩
  inter_subset_convexHull := by
    intro s t hs ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    obtain ⟨k, hik, hjk⟩ := hK i j
    exact (K k).inter_subset_convexHull (hik hi) (hjk hj)

/-- Faces of the directed union are exactly the member faces.
See Hudson pp. 3--5 and M76 derivation 84. -/
theorem directedUnion_faces (K : ι → SimplicialComplex 𝕜 E) (hK : Directed (· ≤ ·) K) :
    (directedUnion K hK).faces = ⋃ i, (K i).faces := rfl

/-- Each member is a subcomplex of the directed union.
See Hudson pp. 3--5 and M76 derivation 84. -/
theorem le_directedUnion (K : ι → SimplicialComplex 𝕜 E) (hK : Directed (· ≤ ·) K)
    (i : ι) : K i ≤ directedUnion K hK :=
  fun _ hs => mem_iUnion.mpr ⟨i, hs⟩

/-- Directed union preserves the exact union of the geometric
carriers. See Hudson pp. 3--5 and M76 derivation 84. -/
theorem directedUnion_space (K : ι → SimplicialComplex 𝕜 E) (hK : Directed (· ≤ ·) K) :
    (directedUnion K hK).space = ⋃ i, (K i).space := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact mem_iUnion.mpr ⟨i, mem_space_iff.mpr ⟨s, hi, hxs⟩⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hi
    exact mem_space_iff.mpr ⟨s, mem_iUnion.mpr ⟨i, hs⟩, hxs⟩

end Geometry.SimplicialComplex
