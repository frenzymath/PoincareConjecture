import PoincareConjecture.Proofs.M76.Dehn.OriginalVertexLinkRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexLinkDoubleCount
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FaceCofaceDoubleCount

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

theorem original_chart_stars_boundary_counts
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {R : Set X} (hFR : frontier R ⊆ R) (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) :
    (2 * Nat.card (K.FaceOfCard 2) + 4 * Nat.card (K.FaceOfCard 4) +
        Nat.card A.vertices =
      3 * Nat.card (K.FaceOfCard 3) + 2 * Nat.card K.vertices) ∧
    (4 * Nat.card (K.FaceOfCard 4) + Nat.card (A.FaceOfCard 3) =
      2 * Nat.card (K.FaceOfCard 3)) ∧
    (3 * Nat.card (A.FaceOfCard 3) = 2 * Nat.card (A.FaceOfCard 2)) ∧
    (2 * Nat.card K.vertices + 2 * Nat.card (K.FaceOfCard 3) +
        Nat.card (A.FaceOfCard 2) =
      2 * Nat.card (K.FaceOfCard 2) + 2 * Nat.card (K.FaceOfCard 4) +
        Nat.card A.vertices + Nat.card (A.FaceOfCard 3)) := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let : Finite (K.FaceOfCard 3) := K.finite_faceOfCard hK 3
  let : Fintype (K.FaceOfCard 3) := Fintype.ofFinite _
  have hA : A.faces.Finite := hK.subset hAK
  let : Finite (A.FaceOfCard 2) := A.finite_faceOfCard hA 2
  let : Fintype (A.FaceOfCard 2) := Fintype.ofFinite _
  have hlocal (p : K.vertices) :
      Nat.card (K.faceLink {p.val}).vertices +
          Nat.card ((K.faceLink {p.val}).FaceOfCard 3) =
        Nat.card ((K.faceLink {p.val}).FaceOfCard 2) +
          if p.val ∈ A.vertices then 1 else 2 := by
    let Q := K.faceLink {p.val}
    let L := Q.vertexAbstractComplex.toPreAbstractSimplicialComplex
    have hQ : Q.faces.Finite := SimplicialComplex.finite_faceLink_faces hK _
    let : Fintype Q.vertices := (Q.finite_vertices_of_finite_faces hQ).fintype
    have hcount := (original_chart_stars_vertex_link_counts K A hK hAK hfull
      hFR H g hg hboundary hstars p.property).2
    have htriangles : Nat.card (Triangle L) = Nat.card (Q.FaceOfCard 3) :=
      Nat.card_congr (Q.vertexFaceEquiv 3)
    have hedges : Nat.card (Edge L) = Nat.card (Q.FaceOfCard 2) :=
      Nat.card_congr (Q.vertexFaceEquiv 2)
    rw [htriangles, hedges] at hcount
    exact hcount
  have hsum := K.sum_vertexLink_local_counts A hAK hK hlocal
  have hpure := exists_tetrahedral_coface_of_original_chart_stars K hK H g hg hstars
  have hfacets := original_chart_stars_facet_incidence
    K hK A hAK hfull H g hg hboundary hpure hstars
  have hfacetCount :
      4 * Nat.card (K.FaceOfCard 4) + Nat.card (A.FaceOfCard 3) =
        2 * Nat.card (K.FaceOfCard 3) := by
    apply K.original_face_coface_count_of_one_two A hAK hK (by decide : 0 < 3)
    intro s
    have hlink :
        {t : Finset E | t ∈ K.faces ∧ t.card = 4 ∧ s.val ⊆ t}.ncard =
          (K.faceLink s.val).vertices.ncard := by
      simpa only [s.property.2] using (K.ncard_faceLink_vertices_eq_cofaces s.val).symm
    rw [hlink]
    by_cases hsA : s.val ∈ A.faces
    · rw [if_pos hsA]
      exact (hfacets s.val s.property.1 s.property.2).1 hsA
    · rw [if_neg hsA]
      exact (hfacets s.val s.property.1 s.property.2).2 hsA
  have hsurface := original_boundary_surface_incidence K A hK hAK
    hFR H g hg hboundary hstars
  have hboundaryCount :
      3 * Nat.card (A.FaceOfCard 3) = 2 * Nat.card (A.FaceOfCard 2) := by
    apply A.original_face_coface_count_of_two hA (by decide : 0 < 2)
    intro s
    have hlink :
        {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s.val ⊆ t}.ncard =
          (A.faceLink s.val).vertices.ncard := by
      simpa only [s.property.2] using (A.ncard_faceLink_vertices_eq_cofaces s.val).symm
    rw [hlink]
    exact hsurface.2.1 s.val s.property.1 s.property.2
  exact ⟨hsum, hfacetCount, hboundaryCount, by omega⟩

end PoincareConjecture.M76
