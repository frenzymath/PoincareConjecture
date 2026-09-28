import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplement
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricSurfaceIncidence










set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] (K : SimplicialComplex ℝ E) [Fintype K.faces]


theorem barycentricNeighborhood_face_iff_vertex_star
    (L : SimplicialComplex ℝ E) (hLK : L ≤ K) {t : Finset E} :
    t ∈ (K.barycentricNeighborhood L).faces ↔
      ∃ v ∈ L.vertices, t ∈ (K.barycentricSubdivision.closedStar v).faces := by
  classical
  constructor
  · intro ht
    obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains t).mp ht.1
    obtain ⟨s, hs, hmin⟩ := a.exists_min_image Finset.card ha
    have hst (u : Finset E) (hu : u ∈ a) : s ⊆ u := by
      rcases hchain s hs u hu with hsu | hus
      · exact hsu
      · exact (Finset.eq_of_subset_of_card_le hus (hmin u hu)).symm.subset
    have hcs : s.centroid ℝ id ∈ t := heq.symm ▸ Finset.mem_image_of_mem _ hs
    obtain ⟨r, hr, ⟨v, hvr, hvL⟩, hrs⟩ := ht.2 _ hcs
    have hrs' : r = s := congrArg Subtype.val (K.faceCentroid_injective
      (a₁ := ⟨r, hr⟩) (a₂ := ⟨s, hfaces s hs⟩) hrs)
    subst r
    refine ⟨v, hvL, ?_⟩
    rw [← K.barycentricDualBlock_singleton_eq_closedStar (hLK hvL)]
    refine ⟨ht.1, ?_⟩
    intro y hy
    obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp (heq ▸ hy)
    exact ⟨u, hfaces u hu, Finset.singleton_subset_iff.mpr (hst u hu hvr), huy⟩
  · rintro ⟨v, hvL, ht⟩
    rw [← K.barycentricDualBlock_singleton_eq_closedStar (hLK hvL)] at ht
    refine ⟨ht.1, ?_⟩
    intro y hy
    obtain ⟨s, hs, hvs, hsy⟩ := ht.2 y hy
    exact ⟨s, hs, ⟨v, hvs (Finset.mem_singleton_self _), hvL⟩, hsy⟩


theorem barycentricNeighborhood_pure_triangles
    (L : SimplicialComplex ℝ E) (hLK : L ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t) :
    ∀ s ∈ (K.barycentricNeighborhood L).faces,
      ∃ t ∈ (K.barycentricNeighborhood L).faces, t.card = 3 ∧ s ⊆ t := by
  classical
  intro s hs
  obtain ⟨v, hvL, hsv⟩ := (K.barycentricNeighborhood_face_iff_vertex_star L hLK).mp hs
  obtain ⟨t, ht, htc, hvst⟩ := K.barycentricSubdivision_pure_triangles hpure
    (insert v s) hsv.2
  have hvt : v ∈ t := hvst (Finset.mem_insert_self _ _)
  have htv : t ∈ (K.barycentricSubdivision.closedStar v).faces := by
    refine ⟨ht, ?_⟩
    simpa only [Finset.insert_eq_of_mem hvt] using ht
  exact ⟨t, (K.barycentricNeighborhood_face_iff_vertex_star L hLK).mpr ⟨v, hvL, htv⟩,
    htc, (Finset.subset_insert _ _).trans hvst⟩

omit [DecidableEq E] in


theorem original_vertex_mem_barycentricNeighborhood_iff
    (L : SimplicialComplex ℝ E) {v : E} (hv : v ∈ K.vertices) :
    v ∈ (K.barycentricNeighborhood L).vertices ↔ v ∈ L.vertices := by
  classical
  constructor
  · intro h
    obtain ⟨s, hs, ⟨w, hws, hwL⟩, hsv⟩ := h.2 v (Finset.mem_singleton_self _)
    have hvs : (⟨s, hs⟩ : K.faces) = ⟨{v}, hv⟩ := K.faceCentroid_injective
      (hsv.trans (Finset.centroid_singleton ℝ id v).symm)
    have hs' : s = {v} := congrArg Subtype.val hvs
    exact (Finset.mem_singleton.mp (hs' ▸ hws)) ▸ hwL
  · intro hvL
    refine ⟨K.vertices_subset_barycentricSubdivision_vertices hv, ?_⟩
    intro y hy
    have hyv := Finset.mem_singleton.mp hy
    exact ⟨{v}, hv, ⟨v, Finset.mem_singleton_self _, hvL⟩,
      (Finset.centroid_singleton ℝ id v).trans hyv.symm⟩



theorem unmarked_vertex_star_le_closedFaceComplement
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {v : E} (hv : v ∈ K.vertices) (hvL : v ∉ L.vertices) :
    K.barycentricSubdivision.closedStar v ≤
      K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L) := by
  classical
  intro s hs
  obtain ⟨t, ht, htc, hvst⟩ := K.barycentricSubdivision_pure_triangles hpure
    (insert v s) hs.2
  have htN : t ∉ (K.barycentricNeighborhood L).faces := by
    intro htN
    have hvN := (K.barycentricNeighborhood L).down_closed htN
      (Finset.singleton_subset_iff.mpr (hvst (Finset.mem_insert_self _ _)))
      (Finset.singleton_nonempty v)
    exact hvL ((K.original_vertex_mem_barycentricNeighborhood_iff L hv).mp hvN)
  exact ⟨hs.1, t, ht, htN, (Finset.subset_insert _ _).trans hvst⟩



theorem closedFaceComplement_derived_face_iff
    (L : SimplicialComplex ℝ E)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    {s : Finset E} :
    s ∈ (K.barycentricSubdivision.closedFaceComplement (K.barycentricNeighborhood L)).faces ↔
      ∃ v ∈ K.vertices, v ∉ L.vertices ∧
        s ∈ (K.barycentricSubdivision.closedStar v).faces := by
  classical
  constructor
  · rintro ⟨hs, t, ht, htN, hst⟩
    obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains t).mp ht
    obtain ⟨m, hm, hmin⟩ := a.exists_min_image Finset.card ha
    have hmu (u : Finset E) (hu : u ∈ a) : m ⊆ u := by
      rcases hchain m hm u hu with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h (hmin u hu)).symm.subset
    obtain ⟨v, hvm⟩ := K.nonempty_of_mem_faces (hfaces m hm)
    have hvK : v ∈ K.vertices := K.down_closed (hfaces m hm)
      (Finset.singleton_subset_iff.mpr hvm) (Finset.singleton_nonempty v)
    have htv : t ∈ (K.barycentricDualBlock {v}).faces := by
      refine ⟨ht, ?_⟩
      intro y hy
      obtain ⟨u, hu, huy⟩ := Finset.mem_image.mp (heq ▸ hy)
      exact ⟨u, hfaces u hu, Finset.singleton_subset_iff.mpr (hmu u hu hvm), huy⟩
    have hvL : v ∉ L.vertices := by
      intro hvL
      apply htN
      refine ⟨ht, ?_⟩
      intro y hy
      obtain ⟨u, hu, hvu, huy⟩ := htv.2 y hy
      exact ⟨u, hu, ⟨v, hvu (Finset.mem_singleton_self _), hvL⟩, huy⟩
    refine ⟨v, hvK, hvL, ?_⟩
    have hstar : t ∈ (K.barycentricSubdivision.closedStar v).faces :=
      (K.barycentricDualBlock_singleton_eq_closedStar hvK) ▸ htv
    exact (K.barycentricSubdivision.closedStar v).down_closed hstar hst
      (K.barycentricSubdivision.nonempty_of_mem_faces hs)
  · rintro ⟨v, hv, hvL, hs⟩
    exact K.unmarked_vertex_star_le_closedFaceComplement L hpure hv hvL hs

end Geometry.SimplicialComplex
