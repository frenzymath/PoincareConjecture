import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.BoundedRegionConvexTriangulation
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionIntrinsicDensity

/-!
# Full cofaces near the interior of a finite geometric carrier

A simplex meeting the carrier interior has an intrinsic-interior
point there. A full face through that point contains the entire
simplex by the geometric intersection law. See Cairns 1940,
pp. 804--806, Hudson 1969, p. 5 and M76 derivation 258.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A face meeting the ambient interior of a finite complex
is contained in a full-dimensional coface, independently of
global carrier convexity. See Cairns pp. 804--806 and M76
derivation 258. -/
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
