import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplement
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.IncidentJointSigns

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]

theorem face_mem_edgeComponent_of_hull_inter
    (K : SimplicialComplex ℝ E)
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {t : Finset E} (ht : t ∈ K.faces)
    (hmeet : (convexHull ℝ (t : Set E) ∩ (K.edgeComponentComplex C).space).Nonempty) :
    t ∈ (K.edgeComponentComplex C).faces := by
  obtain ⟨x, hxt, hxC⟩ := hmeet
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxC
  obtain ⟨v, hvt, hvs⟩ := convexHull_nonempty_iff.mp
    ⟨x, K.inter_subset_convexHull ht hs.1 ⟨hxt, hxs⟩⟩
  have hvC : {v} ∈ (K.edgeComponentComplex C).faces :=
    (K.edgeComponentComplex C).down_closed hs
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty _)
  exact K.edgeComponentComplex_coface C hvC ht (Finset.singleton_subset_iff.mpr hvt)

theorem barycentric_face_mem_edgeComponent_of_hull_inter
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    [Fintype (K.edgeComponentComplex C).faces]
    {t : Finset E} (ht : t ∈ K.barycentricSubdivision.faces)
    (hmeet : (convexHull ℝ (t : Set E) ∩ (K.edgeComponentComplex C).space).Nonempty) :
    t ∈ (K.edgeComponentComplex C).barycentricSubdivision.faces := by
  obtain ⟨s, hs, hts⟩ := K.barycentricSubdivision_isSubdivision.face_subset t ht
  have hsC := K.face_mem_edgeComponent_of_hull_inter C hs
    (hmeet.mono (inter_subset_inter_left _ hts))
  let : Fintype K.barycentricSubdivision.faces := K.barycentricSubdivision_finite.fintype
  let : Fintype (K.edgeComponentComplex C).barycentricSubdivision.faces :=
    (K.edgeComponentComplex C).barycentricSubdivision_finite.fintype
  apply K.barycentricSubdivision.face_mem_subcomplex_of_centroid _
    ((K.edgeComponentComplex C).barycentricSubdivision_mono (K.edgeComponentComplex_le C)) ht
  rw [(K.edgeComponentComplex C).barycentricSubdivision_isSubdivision.space_eq]
  exact (K.edgeComponentComplex C).convexHull_subset_space hsC
    (hts (Finset.centroid_mem_convexHull _ (K.barycentricSubdivision.nonempty_of_mem_faces ht)))

theorem barycentricNeighborhood_edgeComponent
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    [Fintype (K.edgeComponentComplex C).faces]
    (L : SimplicialComplex ℝ E) (hLC : L ≤ K.edgeComponentComplex C) :
    (K.edgeComponentComplex C).barycentricNeighborhood L = K.barycentricNeighborhood L := by
  apply SimplicialComplex.ext
  ext t
  constructor
  · intro ht
    refine ⟨(K.edgeComponentComplex C).barycentricSubdivision_mono
      (K.edgeComponentComplex_le C) ht.1, ?_⟩
    intro x hx
    obtain ⟨s, hs, hmark, hcent⟩ := ht.2 x hx
    exact ⟨s, hs.1, hmark, hcent⟩
  · intro ht
    have hcoarse (x) (hx : x ∈ t) :
        ∃ s ∈ (K.edgeComponentComplex C).faces,
          (∃ v ∈ s, v ∈ L.vertices) ∧ s.centroid ℝ id = x := by
      obtain ⟨s, hs, hmark, hcent⟩ := ht.2 x hx
      obtain ⟨v, hvs, hvL⟩ := hmark
      exact ⟨s, K.edgeComponentComplex_coface C (hLC hvL) hs
        (Finset.singleton_subset_iff.mpr hvs), ⟨v, hvs, hvL⟩, hcent⟩
    refine ⟨K.barycentricSubdivision_full (K.edgeComponentComplex_le C) ht.1 ?_, hcoarse⟩
    intro x hx
    obtain ⟨s, hs, _, hcent⟩ := hcoarse x hx
    exact ((K.edgeComponentComplex C).mem_barycentricSubdivision_vertices_iff x).mpr
      ⟨s, hs, hcent⟩

theorem closed_cut_edgeComponent_space
    (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (C : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    [Fintype (K.edgeComponentComplex C).faces] (N : SimplicialComplex ℝ E) :
    ((K.edgeComponentComplex C).barycentricSubdivision.closedFaceComplement N).space =
      (K.barycentricSubdivision.closedFaceComplement N).space ∩
        (K.edgeComponentComplex C).space := by
  rw [(K.edgeComponentComplex C).barycentricSubdivision.closedFaceComplement_space,
    K.barycentricSubdivision.closedFaceComplement_space]
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    refine ⟨mem_iUnion₂.mpr ⟨t, ⟨(K.edgeComponentComplex C).barycentricSubdivision_mono
      (K.edgeComponentComplex_le C) ht.1, ht.2⟩, hxt⟩, ?_⟩
    rw [← (K.edgeComponentComplex C).barycentricSubdivision_isSubdivision.space_eq]
    exact (K.edgeComponentComplex C).barycentricSubdivision.convexHull_subset_space ht.1 hxt
  · rintro ⟨hx, hxC⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨t, ⟨K.barycentric_face_mem_edgeComponent_of_hull_inter C ht.1
      ⟨x, hxt, hxC⟩, ht.2⟩, hxt⟩

end Geometry.SimplicialComplex
