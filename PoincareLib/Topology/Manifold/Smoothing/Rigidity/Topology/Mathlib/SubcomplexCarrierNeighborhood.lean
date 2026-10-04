import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionIntrinsicDensity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.ClosedStarProjectionCoverage

/-!
# Whole faces retained by a relative carrier neighborhood

Intrinsic-interior density and the geometric intersection law put a
whole face in a subcomplex whenever its carrier contains a relative
neighborhood of one point of that face. See Hudson1969, pp.8--9 and
rigidity019, section2.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A subcomplex containing a relative ambient-carrier neighborhood
at a point of a face contains that entire face. No graph ambient
interior is required. See rigidity019, section2. -/
theorem face_mem_subcomplex_of_carrier_nhds
    {K A : SimplicialComplex ℝ E} (hAK : A ≤ K)
    {s : Finset E} (hs : s ∈ K.faces) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) (hA : A.space ∈ 𝓝[K.space] x) :
    s ∈ A.faces := by
  obtain ⟨U, hU, hxU, hUA⟩ := mem_nhdsWithin.mp hA
  obtain ⟨y, hyi, hyU⟩ :=
    (convex_convexHull ℝ (s : Set E)).intrinsicInterior_inter_open_nonempty
      hU ⟨x, hx, hxU⟩
  have hyA : y ∈ A.space :=
    hUA ⟨hyU, K.convexHull_subset_space hs (intrinsicInterior_subset hyi)⟩
  obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hyA
  exact A.down_closed ht (K.subset_of_mem_intrinsicInterior_face hs (hAK ht) hyi hyt)
    (K.nonempty_of_mem_faces hs)

end Geometry.SimplicialComplex
