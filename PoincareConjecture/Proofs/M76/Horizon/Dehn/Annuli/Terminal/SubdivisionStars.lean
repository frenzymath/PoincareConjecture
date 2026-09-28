import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E]

theorem IsSubdivision.exists_original_vertex_star
    {R K : SimplicialComplex ℝ E} (hRK : R.IsSubdivision K) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ R.vertices) :
    ∃ v ∈ K.vertices, ∀ s ∈ (R.closedStar p).faces,
      ∃ t ∈ (K.closedStar v).faces,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  have hpK := hRK.space_eq.subset (R.vertices_subset_space hp)
  obtain ⟨a, ha, _, hmin, _⟩ :=
    K.exists_minimal_faceStar_neighborhood_of_finite hK ⟨p, hpK⟩
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ha
  refine ⟨v, K.down_closed ha (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty v), ?_⟩
  intro s hs
  obtain ⟨t, ht, hst⟩ := hRK.face_subset (insert p s) hs.2
  have hpt : p ∈ convexHull ℝ (t : Set E) :=
    hst (subset_convexHull ℝ _ (Finset.mem_insert_self p s))
  have hvt := hmin t ht hpt hv
  refine ⟨t, ⟨ht, ?_⟩, ?_⟩
  · simpa only [Finset.insert_eq_of_mem hvt] using ht
  · exact (convexHull_mono (Finset.subset_insert p s)).trans hst

theorem IsSubdivision.exists_original_affine_vertex_star
    {R K : SimplicialComplex ℝ E} (hRK : R.IsSubdivision K) (hK : K.faces.Finite)
    {p : E} (hp : p ∈ R.vertices) :
    ∃ v ∈ K.vertices,
      (R.closedStar p).space ⊆ (K.closedStar v).space ∧
      ∀ f : E → F, (K.closedStar v).AffineOnFaces f → (R.closedStar p).AffineOnFaces f := by
  obtain ⟨v, hv, hfaces⟩ := hRK.exists_original_vertex_star hK hp
  refine ⟨v, hv, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    obtain ⟨t, ht, hst⟩ := hfaces s hs
    exact (K.closedStar v).convexHull_subset_space ht (hst hxs)
  · intro f hf s hs
    obtain ⟨t, ht, hst⟩ := hfaces s hs
    obtain ⟨a, ha⟩ := hf t ht
    exact ⟨a, fun x hx => ha (hst hx)⟩

end Geometry.SimplicialComplex
