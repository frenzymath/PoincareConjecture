import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIntrinsicDensity

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_full_coface_of_hull_meets_interior
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces)
    (hmeet : (convexHull ℝ (s : Set E) ∩ interior K.space).Nonempty) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = Module.finrank ℝ E + 1 := by
  obtain ⟨x, hxs, hxint⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
      isOpen_interior hmeet
  obtain ⟨t, ht, htcard, hxt⟩ := K.exists_full_face_of_mem_interior hK hxint
  exact ⟨t, ht, K.subset_of_mem_intrinsicInterior_face hs ht hxs hxt, htcard⟩

end Geometry.SimplicialComplex
