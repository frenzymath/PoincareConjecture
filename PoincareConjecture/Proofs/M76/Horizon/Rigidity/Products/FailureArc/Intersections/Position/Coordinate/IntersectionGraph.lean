import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Affine.TransverseFaceGraph

set_option autoImplicit false
open Set Geometry Module

namespace Geometry.SimplicialComplex

theorem exists_surface_intersection_graph_of_position
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 3)
    (A T : SimplicialComplex ℝ E) (hA : A.faces.Finite) (hT : T.faces.Finite)
    (hAc : ∀ a ∈ A.faces, a.card ≤ 3) (hTc : ∀ t ∈ T.faces, t.card ≤ 3)
    {Z : Set E} (Q : Finset (AffineSubspace ℝ E))
    (hQ : ∀ L ∈ Q, finrank ℝ L.direction ≤ 1)
    (hprotected : ∀ x ∈ Z ∩ T.space, ∃ L ∈ Q, x ∈ L)
    (hposition : ∀ a ∈ A.faces, convexHull ℝ (a : Set E) ⊆ Z ∨
      ∀ t ∈ T.faces, affineSpan ℝ ((a : Set E) ∪ (t : Set E)) = ⊤ ∨
        Disjoint (intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
          (convexHull ℝ (t : Set E))) :
    ∃ G : SimplicialComplex ℝ E, G.faces.Finite ∧ G.space = A.space ∩ T.space ∧
      ∀ face ∈ G.faces, face.card ≤ 2 := by
  classical
  have hlines (t : T.faces) : ∃ L : Finset (AffineSubspace ℝ E),
      (∀ V ∈ L, finrank ℝ V.direction ≤ 1) ∧
      ∀ x ∈ A.space ∩ convexHull ℝ (t.val : Set E), ∃ V ∈ L, x ∈ V := by
    exact A.exists_finite_line_cover_of_face_position hA hdim hAc
      (T.nonempty_of_mem_faces t.property) (hTc t t.property) Q hQ
      (fun x hx => hprotected x ⟨hx.1, T.convexHull_subset_space t.property hx.2⟩)
      (fun a ha => (hposition a ha).imp_right (fun hh => hh t t.property))
  choose L hL hcover using hlines
  let : Fintype T.faces := hT.fintype
  let lines := Finset.univ.biUnion L
  have hdimlines : ∀ V ∈ lines, finrank ℝ V.direction ≤ 1 := by
    intro V hV
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hV
    exact hL t V ht
  obtain ⟨G, hG, hGs⟩ := A.exists_finite_triangulation_inter T hA hT
  refine ⟨G, hG, hGs, ?_⟩
  intro face hface
  apply G.face_card_le_of_finite_affine_cover lines hdimlines _ hface
  intro x hx
  have hxAT := hGs.subset hx
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxAT.2
  obtain ⟨V, hVL, hxV⟩ := hcover ⟨t, ht⟩ x ⟨hxAT.1, hxt⟩
  exact ⟨V, Finset.mem_biUnion.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, hVL⟩, hxV⟩

end Geometry.SimplicialComplex
