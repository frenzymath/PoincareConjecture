import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.DerivedComplementLinks
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSurfaceIncidence

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

open Classical in

theorem derived_closed_cut_surface_incidence
    (K L : SimplicialComplex ℝ E) [Fintype K.faces] (hLK : L ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space) :
    let N := K.barycentricNeighborhood L
    let C := K.barycentricSubdivision.closedFaceComplement N
    C.faces.Finite ∧
      (∀ s ∈ C.faces, ∃ t ∈ C.faces, t.card = 3 ∧ s ⊆ t) ∧
      (∀ v ∈ C.vertices, IsConnected (C.link v).space) ∧
      ∀ s ∈ C.faces, s.card = 2 →
        {t : Finset E | t ∈ C.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
          if s ∈ N.faces then 1 else 2 := by
  have hdim : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, _, htc, hst⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq htc
  refine ⟨K.barycentricSubdivision.closedFaceComplement_finite _
    K.barycentricSubdivision_finite,
    K.barycentricSubdivision.closedFaceComplement_pure _
      (K.barycentricSubdivision_pure_triangles hpure),
    K.closedFaceComplement_derived_links L hLK hpure hlinks, ?_⟩
  intro s hs hsc
  exact K.barycentricSubdivision.closedFaceComplement_edge_coface_count _
    K.barycentricSubdivision_finite (K.barycentricNeighborhood_le L)
    (K.barycentricSubdivision_pure_triangles hpure)
    (K.barycentricNeighborhood_pure_triangles L hLK hpure)
    (K.barycentricSubdivision_two_triangle_cofaces hdim hcofaces) hs hsc

end Geometry.SimplicialComplex
