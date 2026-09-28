import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkDimension
import PoincareConjecture.Proofs.M76.Smoothing.LinkIncidencePlanes
import PoincareConjecture.Proofs.M76.Smoothing.SmallNormalFacePlanes

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Smoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem contractible_positiveFaceStarPlanes (K : SimplicialComplex ℝ E)
    (hK : AffineIndependent ℝ ((↑) : K.vertices → E)) (hfinite : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 4)
    (hedges : ∀ t ∈ K.faces, t.card = 2 → IsConnected (K.faceLink t).space)
    (htriangles : ∀ t ∈ K.faces, t.card = 3 → (K.faceLink t).vertices.ncard = 2)
    {s : Finset E} (hs : s ∈ K.faces) (hpositive : 2 ≤ s.card) :
    ContractibleSpace (SecantTransversePlaneSpace 3 (K.closedFaceStar s).space) := by
  have hle := hbound s hs
  have hcases : s.card = 2 ∨ s.card = 3 ∨ s.card = 4 := by omega
  rcases hcases with htwo | hthree | hfour
  · have hdim : ∀ t ∈ (K.faceLink s).faces, t.card ≤ 2 := by
      intro t ht
      have h := K.card_add_card_le_of_mem_faceLink hbound s ht
      omega
    have hlinks : ∀ u : (K.faceLink s).vertices,
        (K.faceLink (s ∪ {u.val})).vertices.ncard = 2 := by
      intro u
      apply htriangles (s ∪ {u.val}) u.property.2.2
      rw [Finset.card_union_of_disjoint u.property.2.1, Finset.card_singleton, htwo]
    have h := contractible_faceStarPlanes_of_link_incidence K hK hfinite hs
      (hedges s hs htwo) hdim hlinks
    rwa [K.finrank_faceDirection_of_card hs (n := 1) htwo] at h
  · have hdim : ∀ t ∈ (K.faceLink s).faces, t.card ≤ 1 := by
      intro t ht
      have h := K.card_add_card_le_of_mem_faceLink hbound s ht
      omega
    obtain ⟨u, v, huv, hlink⟩ := (K.faceLink s).exists_faces_eq_two_singletons hdim
      (htriangles s hs hthree)
    have h := contractible_twoPointFaceStarPlanes K hK hs huv hlink
    rwa [K.finrank_faceDirection_of_card hs (n := 2) hthree] at h
  · have hlink := K.faceLink_faces_eq_empty_of_card_eq hbound hfour
    have h := contractible_emptyLinkFaceStarPlanes K hK hs hlink
    rwa [K.finrank_faceDirection_of_card hs (n := 3) hfour] at h

end PoincareConjecture.M76.Smoothing
