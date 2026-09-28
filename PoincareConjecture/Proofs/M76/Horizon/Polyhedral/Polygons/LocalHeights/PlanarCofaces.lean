import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Polygons.LocalHeights.CrossingLabels
import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem triangleCrossingEdges_two_cofaces_of_boundary_avoids
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 2) (A : Finset E → E →ᵃ[ℝ] ℝ)
    (f : E → X) (F : Set X)
    (hzero : ∀ t ∈ K.faces, t.card = 3 →
      ∀ x ∈ convexHull ℝ (t : Set E), A t x = 0 ↔ f x ∈ F)
    (hboundary : ∀ x ∈ frontier K.space, f x ∉ F)
    (e : K.triangleCrossingEdges A) :
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}.ncard = 2 := by
  let q := K.triangleCrossingPoint A e
  have hq := K.triangleCrossingPoint_mem A e
  have ht := K.triangleCrossingTriangle_spec A e
  have hqF : f q ∈ F := (hzero _ ht.1 ht.2.1 q (convexHull_mono ht.2.2.1 hq.1)).mp hq.2
  have hqS : q ∈ K.space := K.convexHull_subset_space e.property.1 hq.1
  have hqint : q ∈ interior K.space := by
    by_contra hn
    exact hboundary q (show q ∈ closure K.space \ interior K.space from
      ⟨subset_closure hqS, hn⟩) hqF
  have hcard := K.triangleCrossingEdge_card A e
  have hlink := K.faceLink_ncard_eq_two_of_hull_meets_interior hK e.property.1
    (hcard.trans hdim.symm) ⟨q, hq.1, hqint⟩
  rw [K.ncard_faceLink_vertices_eq_cofaces, hcard] at hlink
  exact hlink

end Geometry.SimplicialComplex
