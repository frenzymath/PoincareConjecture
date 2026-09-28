import PoincareConjecture.Proofs.M76.Mathlib.BarycentricFullSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.VertexInducedSubcomplex











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]




noncomputable def barycentricNeighborhood (L : SimplicialComplex ℝ E) :
    SimplicialComplex ℝ E :=
  K.barycentricSubdivision.vertexSubcomplex
    {x | ∃ s ∈ K.faces, (∃ v ∈ s, v ∈ L.vertices) ∧ s.centroid ℝ id = x}




theorem barycentricNeighborhood_finite (L : SimplicialComplex ℝ E) :
    (K.barycentricNeighborhood L).faces.Finite :=
  K.barycentricSubdivision.vertexSubcomplex_finite _ K.barycentricSubdivision_finite



theorem barycentricNeighborhood_le (L : SimplicialComplex ℝ E) :
    K.barycentricNeighborhood L ≤ K.barycentricSubdivision :=
  K.barycentricSubdivision.vertexSubcomplex_le _




theorem mem_barycentricNeighborhood_of_inter_nonempty
    {L : SimplicialComplex ℝ E} [Finite L.faces] (hLK : L ≤ K)
    {t : Finset E} (ht : t ∈ K.barycentricSubdivision.faces)
    (hne : (convexHull ℝ (t : Set E) ∩ L.space).Nonempty) :
    t ∈ (K.barycentricNeighborhood L).faces := by
  classical
  let : Fintype L.faces := Fintype.ofFinite L.faces
  obtain ⟨x, hxt, hxL⟩ := hne
  have hxL' : x ∈ L.barycentricSubdivision.space :=
    L.barycentricSubdivision_isSubdivision.space_eq.symm ▸ hxL
  obtain ⟨u, hu, hxu⟩ := mem_space_iff.mp hxL'
  have hux : x ∈ convexHull ℝ ((t : Set E) ∩ (u : Set E)) :=
    K.barycentricSubdivision.inter_subset_convexHull ht
      (L.barycentricSubdivision_mono hLK hu) ⟨hxt, hxu⟩
  obtain ⟨z, hzt, hzu⟩ := convexHull_nonempty_iff.mp ⟨x, hux⟩
  have hzL : z ∈ L.barycentricSubdivision.vertices :=
    L.barycentricSubdivision.down_closed hu (Finset.singleton_subset_iff.mpr hzu)
      (Finset.singleton_nonempty z)
  obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
    (K.barycentricSubdivision_faces_of_face_chains t).mp ht
  obtain ⟨tau, htau, hctau⟩ := Finset.mem_image.mp (heq ▸ hzt)
  have htauL : tau ∈ L.faces :=
    (K.faceCentroid_mem_barycentricSubdivision_iff hLK ⟨tau, hfaces tau htau⟩).mp
      (hctau.symm ▸ hzL)
  refine ⟨ht, ?_⟩
  intro y hy
  obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp (heq ▸ hy)
  refine ⟨s, hfaces s hs, ?_, hcs⟩
  rcases hchain s hs tau htau with hst | hts
  · obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (hfaces s hs)
    exact ⟨v, hv, L.down_closed htauL (Finset.singleton_subset_iff.mpr (hst hv))
      (Finset.singleton_nonempty v)⟩
  · obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces htauL
    exact ⟨v, hts hv, L.down_closed htauL (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)⟩




theorem space_subset_barycentricNeighborhood
    {L : SimplicialComplex ℝ E} [Finite L.faces] (hLK : L ≤ K) :
    L.space ⊆ (K.barycentricNeighborhood L).space := by
  intro x hx
  have hxK : x ∈ K.space := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact K.convexHull_subset_space (hLK hs) hxs
  have hxK' : x ∈ K.barycentricSubdivision.space :=
    K.barycentricSubdivision_isSubdivision.space_eq.symm ▸ hxK
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxK'
  exact (K.barycentricNeighborhood L).convexHull_subset_space
    (K.mem_barycentricNeighborhood_of_inter_nonempty hLK ht ⟨x, hxt, hx⟩) hxt





theorem exists_open_barycentricNeighborhood
    {L : SimplicialComplex ℝ E} [Finite L.faces] (hLK : L ≤ K) :
    ∃ U : Set E, IsOpen U ∧ L.space ⊆ U ∧
      U ∩ K.space ⊆ (K.barycentricNeighborhood L).space := by
  classical
  let B : Set (Finset E) :=
    {t | t ∈ K.barycentricSubdivision.faces ∧ t ∉ (K.barycentricNeighborhood L).faces}
  have hB : B.Finite := K.barycentricSubdivision_finite.subset (fun _ ht => ht.1)
  let bad : Set E := ⋃ t ∈ B, convexHull ℝ (t : Set E)
  have hbad : IsClosed bad := hB.isClosed_biUnion
    (fun t _ => t.finite_toSet.isClosed_convexHull ℝ)
  refine ⟨badᶜ, hbad.isOpen_compl, ?_, ?_⟩
  · intro x hx hxb
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxb
    exact ht.2 (K.mem_barycentricNeighborhood_of_inter_nonempty hLK ht.1 ⟨x, hxt, hx⟩)
  · rintro x ⟨hx, hxK⟩
    have hxK' : x ∈ K.barycentricSubdivision.space :=
      K.barycentricSubdivision_isSubdivision.space_eq.symm ▸ hxK
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxK'
    have htN : t ∈ (K.barycentricNeighborhood L).faces := by
      by_contra hnot
      exact hx (mem_iUnion₂.mpr ⟨t, ⟨ht, hnot⟩, hxt⟩)
    exact (K.barycentricNeighborhood L).convexHull_subset_space htN hxt

end Geometry.SimplicialComplex
