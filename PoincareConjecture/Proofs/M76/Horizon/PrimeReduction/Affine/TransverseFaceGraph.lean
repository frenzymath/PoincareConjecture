import PoincareConjecture.Proofs.M76.PrimeReduction.FiniteSurfaceEdgeContacts
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation

set_option autoImplicit false

open Set Module

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finrank_affine_intersection_le_one
    (hdim : finrank ℝ E = 3) {s t : Finset E}
    (hs : s.Nonempty) (ht : t.Nonempty) (hsc : s.card ≤ 3) (htc : t.card ≤ 3)
    (hspan : affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤)
    (hmeet : (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty) :
    finrank ℝ (affineSpan ℝ (s : Set E) ⊓ affineSpan ℝ (t : Set E)).direction ≤ 1 := by
  obtain ⟨x, hxs, hxt⟩ := hmeet
  have hjoin : affineSpan ℝ (s : Set E) ⊔ affineSpan ℝ (t : Set E) = ⊤ := by
    rw [← AffineSubspace.span_union]
    exact hspan
  have hrank := (affineSpan ℝ (s : Set E)).finrank_inf_add_ambient_of_mem_of_sup_top
    (affineSpan ℝ (t : Set E)) (convexHull_subset_affineSpan (s := (s : Set E)) hxs)
      (convexHull_subset_affineSpan (s := (t : Set E)) hxt) hjoin
  have hsbound := finrank_affineSpan_finset_le hs (d := 2) hsc
  have htbound := finrank_affineSpan_finset_le ht (d := 2) htc
  omega

namespace SimplicialComplex

theorem exists_finite_line_cover_of_face_position
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : finrank ℝ E = 3) (hcard : ∀ s ∈ K.faces, s.card ≤ 3)
    {t : Finset E} (ht : t.Nonempty) (htc : t.card ≤ 3) {Z : Set E}
    (Q : Finset (AffineSubspace ℝ E))
    (hQ : ∀ A ∈ Q, finrank ℝ A.direction ≤ 1)
    (hprotected : ∀ x ∈ Z ∩ convexHull ℝ (t : Set E), ∃ A ∈ Q, x ∈ A)
    (hposition : ∀ s ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ Z ∨
        affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
            (convexHull ℝ (t : Set E))) :
    ∃ L : Finset (AffineSubspace ℝ E),
      (∀ A ∈ L, finrank ℝ A.direction ≤ 1) ∧
      ∀ x ∈ K.space ∩ convexHull ℝ (t : Set E), ∃ A ∈ L, x ∈ A := by
  classical
  let T := hK.toFinset.filter fun s : Finset E =>
    affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∧
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty
  let I (s : Finset E) := affineSpan ℝ (s : Set E) ⊓ affineSpan ℝ (t : Set E)
  refine ⟨Q ∪ T.image I, ?_, ?_⟩
  · intro A hA
    rcases Finset.mem_union.mp hA with hAQ | hAT
    · exact hQ A hAQ
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hAT
      obtain ⟨hsK, hspan, hmeet⟩ := Finset.mem_filter.mp hs
      have hsK' : s ∈ K.faces := hK.mem_toFinset.mp hsK
      exact finrank_affine_intersection_le_one hdim (K.nonempty_of_mem_faces hsK')
        ht (hcard s hsK') htc hspan hmeet
  · rintro x ⟨hxK, hxt⟩
    obtain ⟨s, hs, hxs⟩ := K.exists_face_intrinsicInterior_of_finite hK hxK
    rcases hposition s hs with hz | hspan | hdisj
    · obtain ⟨A, hAQ, hxA⟩ := hprotected x ⟨hz (intrinsicInterior_subset hxs), hxt⟩
      exact ⟨A, Finset.mem_union_left _ hAQ, hxA⟩
    · refine ⟨I s, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, ?_, rfl⟩), ?_⟩
      · exact Finset.mem_filter.mpr ⟨hK.mem_toFinset.mpr hs, hspan,
          x, intrinsicInterior_subset hxs, hxt⟩
      · exact ⟨convexHull_subset_affineSpan (s := (s : Set E)) (intrinsicInterior_subset hxs),
          convexHull_subset_affineSpan (s := (t : Set E)) hxt⟩
    · exact (disjoint_left.mp hdisj hxs hxt).elim

theorem intersection_face_card_le_two_of_face_position
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : finrank ℝ E = 3) (hcard : ∀ s ∈ K.faces, s.card ≤ 3)
    {t : Finset E} (ht : t.Nonempty) (htc : t.card ≤ 3) {Z : Set E}
    (Q : Finset (AffineSubspace ℝ E))
    (hQ : ∀ A ∈ Q, finrank ℝ A.direction ≤ 1)
    (hprotected : ∀ x ∈ Z ∩ convexHull ℝ (t : Set E), ∃ A ∈ Q, x ∈ A)
    (hposition : ∀ s ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ Z ∨
        affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
            (convexHull ℝ (t : Set E)))
    (hJ : J.space ⊆ K.space ∩ convexHull ℝ (t : Set E)) :
    ∀ s ∈ J.faces, s.card ≤ 2 := by
  obtain ⟨L, hL, hcover⟩ := K.exists_finite_line_cover_of_face_position hK hdim hcard
    ht htc Q hQ hprotected hposition
  exact fun s hs => J.face_card_le_of_finite_affine_cover L hL
    (fun x hx => hcover x (hJ hx)) hs

theorem exists_face_intersection_graph_of_face_position
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : finrank ℝ E = 3) (hcard : ∀ s ∈ K.faces, s.card ≤ 3)
    {t : Finset E} (ht : t.Nonempty) (htc : t.card ≤ 3) {Z : Set E}
    (Q : Finset (AffineSubspace ℝ E))
    (hQ : ∀ A ∈ Q, finrank ℝ A.direction ≤ 1)
    (hprotected : ∀ x ∈ Z ∩ convexHull ℝ (t : Set E), ∃ A ∈ Q, x ∈ A)
    (hposition : ∀ s ∈ K.faces,
      convexHull ℝ (s : Set E) ⊆ Z ∨
        affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤ ∨
          Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
            (convexHull ℝ (t : Set E))) :
    ∃ J : SimplicialComplex ℝ E, J.faces.Finite ∧
      J.space = K.space ∩ convexHull ℝ (t : Set E) ∧
      ∀ s ∈ J.faces, s.card ≤ 2 := by
  obtain ⟨T, hT, hTs, _⟩ := exists_finite_triangulation_iUnion_finiteHull
    (fun _ : Unit => t)
  have hTspace : T.space = convexHull ℝ (t : Set E) := by
    simpa only [iUnion_const] using hTs
  obtain ⟨J, hJ, hJs⟩ := K.exists_finite_triangulation_inter T hK hT
  rw [hTspace] at hJs
  exact ⟨J, hJ, hJs, K.intersection_face_card_le_two_of_face_position J hK hdim
    hcard ht htc Q hQ hprotected hposition hJs.subset⟩

end SimplicialComplex
end Geometry
