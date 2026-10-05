import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConvexBoundaryRadial
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.SimplicialSubdivision

/-!
# Position-vector independence under face refinement

An independent radial simplex lies on a linear functional's
level one. Every affine simplex contained in it consequently
has independent position vectors. This retains the radial
cone hypotheses under subdivision. See Cairns 1940, p. 802,
Hudson 1969, pp. 12--14 and M76 derivation 248.
-/

set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Refining a simplex with independent position vectors
preserves position-vector independence. See Cairns p. 802
and M76 derivation 248. -/
theorem AffineIndependent.linearIndependent_of_convexHull_subset
    {s t : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E))
    (ht : LinearIndependent ℝ ((↑) : t → E))
    (hsub : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) :
    LinearIndependent ℝ ((↑) : s → E) := by
  obtain ⟨L, hL⟩ := ht.exists_eq_one_on_convexHull
  exact hs.linearIndependent_of_linear_level L one_ne_zero
    (fun v => hL v (hsub (subset_convexHull ℝ _ v.property)))

namespace Geometry.SimplicialComplex

/-- Face containment in radial simplices preserves all the
linear-independence hypotheses for coning at zero. See
Cairns p. 802 and M76 derivation 248. -/
theorem linearIndependent_faces_of_face_containment
    (J K : SimplicialComplex ℝ E)
    (hK : ∀ t ∈ K.faces, LinearIndependent ℝ ((↑) : t → E))
    (hfaces : ∀ s ∈ J.faces, ∃ t ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) :
    ∀ s ∈ J.faces, LinearIndependent ℝ ((↑) : s → E) := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  exact (J.indep hs).linearIndependent_of_convexHull_subset (hK t ht) hst

/-- Subdivision retains position-vector independence of
every face. See Hudson pp. 12--14 and derivation 248. -/
theorem IsSubdivision.linearIndependent_faces
    {J K : SimplicialComplex ℝ E} (hJK : J.IsSubdivision K)
    (hK : ∀ t ∈ K.faces, LinearIndependent ℝ ((↑) : t → E)) :
    ∀ s ∈ J.faces, LinearIndependent ℝ ((↑) : s → E) :=
  J.linearIndependent_faces_of_face_containment K hK hJK.face_subset

end Geometry.SimplicialComplex
