import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaries

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem original_triangle_eq_of_common_refined_triangle
    (K L M : SimplicialComplex ℝ E) (hdim : Module.finrank ℝ E = 2)
    {s t r : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hscard : s.card = 3) (htcard : t.card = 3)
    (hLS : L.space ⊆ convexHull ℝ (s : Set E))
    (hMT : M.space ⊆ convexHull ℝ (t : Set E))
    (hrL : r ∈ L.faces) (hrM : r ∈ M.faces) (hrcard : r.card = 3) : s = t := by
  have hc := L.triangle_centroid_mem_interior hdim hrL hrcard
  have hcS := interior_mono ((L.convexHull_subset_space hrL).trans hLS) hc
  have hcT := interior_mono ((M.convexHull_subset_space hrM).trans hMT) hc
  by_contra hne
  have hfront := K.distinct_triangle_inter_subset_frontiers hs ht hscard htcard hne
    ⟨interior_subset hcS, interior_subset hcT⟩
  exact hfront.1.2 hcS

theorem refined_triangle_owner_unique (K : SimplicialComplex ℝ E)
    (hdim : Module.finrank ℝ E = 2)
    (C : {s : K.faces // s.val.card = 3} → SimplicialComplex ℝ E)
    (hCS : ∀ s, (C s).space ⊆ convexHull ℝ (s.val.val : Set E))
    {s t : {s : K.faces // s.val.card = 3}} {r : Finset E}
    (hrs : r ∈ (C s).faces) (hrt : r ∈ (C t).faces) (hrcard : r.card = 3) : s = t := by
  apply Subtype.ext
  apply Subtype.ext
  exact K.original_triangle_eq_of_common_refined_triangle (C s) (C t) hdim
    s.val.property t.val.property s.property t.property (hCS s) (hCS t) hrs hrt hrcard

end Geometry.SimplicialComplex
