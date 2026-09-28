import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier
import PoincareConjecture.Proofs.M76.Mathlib.AffineVertexExtension
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : SimplicialComplex ℝ E) [Fintype K.faces]





theorem exists_barycentricNeighborhood_retraction
    {L : SimplicialComplex ℝ E} [Finite L.faces] (hLK : L ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) :
    ∃ r : E → E, (K.barycentricNeighborhood L).AffineOnFaces r ∧
      MapsTo r (K.barycentricNeighborhood L).space L.space ∧ EqOn r id L.space := by
  classical
  let : Fintype L.faces := Fintype.ofFinite L.faces
  let q (s : Finset E) := s.filter (fun v => v ∈ L.vertices)
  have hqne {s : Finset E} (hs : ∃ v ∈ s, v ∈ L.vertices) : (q s).Nonempty := by
    obtain ⟨v, hv, hvL⟩ := hs
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, hvL⟩⟩
  have hqface {s : Finset E} (hs : s ∈ K.faces) (hmeet : ∃ v ∈ s, v ∈ L.vertices) :
      q s ∈ L.faces := by
    apply hfull _ (K.down_closed hs (Finset.filter_subset _ _) (hqne hmeet))
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  let v : E → E := fun x =>
    if hx : ∃ s : K.faces, s.val.centroid ℝ id = x then (q hx.choose.val).centroid ℝ id
    else 0
  have hv (s : K.faces) : v (s.val.centroid ℝ id) = (q s.val).centroid ℝ id := by
    dsimp only [v]
    split_ifs with hx
    · have heq : hx.choose = s := K.faceCentroid_injective hx.choose_spec
      rw [heq]
    · exact (hx ⟨s, rfl⟩).elim
  obtain ⟨r, hr, hrverts⟩ := K.barycentricSubdivision.exists_affineOnFaces_eqOn_vertices v
  have hrv (s : K.faces) : r (s.val.centroid ℝ id) = (q s.val).centroid ℝ id :=
    (hrverts ((K.mem_barycentricSubdivision_vertices_iff _).mpr
      ⟨s.val, s.property, rfl⟩)).trans (hv s)
  have hrN : (K.barycentricNeighborhood L).AffineOnFaces r :=
    hr.of_face_containment (fun t ht => ⟨t, ht.1, Subset.rfl⟩)
  refine ⟨r, hrN, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    obtain ⟨a, ha, hfaces, hchain, heq⟩ :=
      (K.barycentricSubdivision_faces_of_face_chains t).mp ht.1
    have hmeet (s : Finset E) (hs : s ∈ a) : ∃ z ∈ s, z ∈ L.vertices := by
      have hcenter : s.centroid ℝ id ∈ t :=
        heq.symm ▸ Finset.mem_image.mpr ⟨s, hs, rfl⟩
      obtain ⟨u, hu, humeet, hcu⟩ := ht.2 _ hcenter
      have hus : (⟨u, hu⟩ : K.faces) = ⟨s, hfaces s hs⟩ := K.faceCentroid_injective hcu
      have hus' : u = s := congrArg Subtype.val hus
      simpa only [hus'] using humeet
    obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
    have hqm : q m ∈ L.faces := hqface (hfaces m hm) (hmeet m hm)
    have himage : r '' (t : Set E) ⊆ convexHull ℝ (q m : Set E) := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (heq ▸ hz)
      rw [hrv ⟨s, hfaces s hs⟩]
      have hsm : s ⊆ m := by
        rcases hchain s hs m hm with h | h
        · exact h
        · exact hmax hs h
      have hqm_sub : q s ⊆ q m := by
        intro z hz
        have hz' := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨hsm hz'.1, hz'.2⟩
      exact convexHull_mono hqm_sub ((q s).centroid_mem_convexHull (hqne (hmeet s hs)))
    apply L.convexHull_subset_space hqm
    apply convexHull_min himage (convex_convexHull ℝ _)
    rw [← hr.image_convexHull ht.1]
    exact mem_image_of_mem r hxt
  · have hrL : L.barycentricSubdivision.AffineOnFaces r :=
      hr.of_face_containment
        (fun t ht => ⟨t, L.barycentricSubdivision_mono hLK ht, Subset.rfl⟩)
    have heq : EqOn r id L.barycentricSubdivision.space :=
      hrL.eqOn_of_eqOn_vertices
        (L.barycentricSubdivision.affineOnFaces_affine (ContinuousAffineMap.id ℝ E)) (by
          intro x hx
          obtain ⟨s, hs, hcs⟩ := (L.mem_barycentricSubdivision_vertices_iff x).mp hx
          have hqs : q s = s := Finset.filter_eq_self.mpr (fun z hz =>
            L.down_closed hs (Finset.singleton_subset_iff.mpr hz) (Finset.singleton_nonempty z))
          simpa only [hqs, hcs, id_eq] using hrv ⟨s, hLK hs⟩)
    rwa [L.barycentricSubdivision_isSubdivision.space_eq] at heq

end Geometry.SimplicialComplex
