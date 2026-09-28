import PoincareConjecture.Proofs.M76.Dehn.OriginalVertexLinkIncidence
import PoincareConjecture.Proofs.M76.Dehn.OriginalVertexLinkExactness
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTriangleIncidence
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleIncidenceRanks

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]

open Classical in

theorem original_chart_stars_vertex_link_counts
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {R : Set X} (hFR : frontier R ⊆ R) (H : R ≃ₜ K.space) (g : E → R)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ A.space)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)))
    {p : E} (hp : p ∈ K.vertices) :
    let Q := K.faceLink {p}
    let L := Q.vertexAbstractComplex.toPreAbstractSimplicialComplex
    (triangleGraph L).Connected ∧
      Nat.card Q.vertices + Nat.card (Triangle L) =
        Nat.card (Edge L) + if p ∈ A.vertices then 1 else 2 := by
  classical
  let Q := K.faceLink {p}
  let L := Q.vertexAbstractComplex.toPreAbstractSimplicialComplex
  obtain ⟨hpure, hconn, hlinks, hcounts, hboundaryEdge, hinteriorEdges⟩ :=
    original_chart_stars_vertex_link_incidence K A hK hAK hfull
      hFR H g hg hboundary hstars hp
  have hQ : Q.faces.Finite := SimplicialComplex.finite_faceLink_faces hK {p}
  let : Fintype Q.vertices := (Q.finite_vertices_of_finite_faces hQ).fintype
  have hedge := Q.connected_edgeGraph_of_isConnected hQ hconn
  have htri := Q.vertex_triangleGraph_connected
    (Q.triangleGraph_connected_of_isConnected hQ hpure hconn hlinks)
  have hexact := original_chart_stars_vertex_link_edge_exact
    K hK A H g hg hboundary hstars hp
  have hlabelCount (e : Edge L) :
      (triangleCofaces L e).card =
        if insert p (e.val.map (Function.Embedding.subtype _)) ∈ A.faces then 1 else 2 := by
    rw [Q.triangleCofaces_card_eq_original e]
    apply hcounts _ e.property.1
    simpa only [Finset.card_map] using e.property.2
  refine ⟨htri, ?_⟩
  by_cases hpA : p ∈ A.vertices
  · rw [if_pos hpA]
    refine Q.vertexAbstractComplex.triangle_incidence_count_of_one_coface
      hedge hexact ?_ htri.preconnected ?_
    · intro e
      rw [hlabelCount e]
      split_ifs <;> omega
    · obtain ⟨e, he, hec, hcount⟩ := hboundaryEdge hpA
      let eg : Edge Q.toPreAbstractSimplicialComplex := ⟨e, he, hec⟩
      let ev : Edge L := (Q.vertexFaceEquiv 2).symm eg
      refine ⟨ev, ?_⟩
      rw [Q.triangleCofaces_card_eq_original ev]
      change {t : Finset E | t ∈ Q.faces ∧ t.card = 3 ∧
        ((Q.vertexFaceEquiv 2).symm eg).val.map (Function.Embedding.subtype _) ⊆ t}.ncard = 1
      rw [Q.vertexFaceEquiv_symm_map]
      exact hcount
  · rw [if_neg hpA]
    refine Q.vertexAbstractComplex.triangle_incidence_count_of_two_cofaces
      hedge hexact ?_ htri
    intro e
    rw [Q.triangleCofaces_card_eq_original e]
    apply hinteriorEdges hpA _ e.property.1
    simpa only [Finset.card_map] using e.property.2

end PoincareConjecture.M76
