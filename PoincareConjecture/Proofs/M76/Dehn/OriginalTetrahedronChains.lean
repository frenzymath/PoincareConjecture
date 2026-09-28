import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryChains
import PoincareConjecture.Proofs.M76.Dehn.OriginalChartConnectedLinks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTetrahedronAdjacency
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.RelativeTetrahedronChains
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalBoundaryLinks

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {G X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [DecidableEq G] [TopologicalSpace X]
  (K : SimplicialComplex ℝ G) (hK : K.faces.Finite) [Fintype K.vertices]
  (L : SimplicialComplex ℝ G) (hLK : L ≤ K)
  (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ L.vertices) → s ∈ L.faces)
  {N : Set X} (hN : IsClosed N) (J : N ≃ₜ K.space) (F : X → G) (g : G → N)
  (hJF : ∀ x : N, (J x : G) = F x)
  (hg : ∀ z : K.space, (g z : X) = (J.symm z : X))
  (hLs : L.space = F '' frontier N)
  (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
  (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
    MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
    (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
    (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
      ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)))

include hK hLK hfull hN J F g hJF hg hLs hpure hstars

omit [Fintype K.vertices] in

theorem original_chart_stars_tetrahedron_connected (hconn : IsConnected K.space) :
    (tetrahedronGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex).Connected := by
  have hboundary (z : G) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier N ↔ z ∈ L.space := by
    rw [hLs]
    exact PoincareConjecture.M76.original_model_mem_image_iff J F g hJF hg
      hN.frontier_subset ⟨z, hz⟩
  have hlinks := PoincareConjecture.M76.original_chart_stars_connected_links
    K hK L hLK hfull J g hg hboundary hstars
  exact K.vertex_tetrahedronGraph_connected
    (K.tetrahedronGraph_connected_of_isConnected hK hpure hconn hlinks)

open Classical in

theorem original_chart_stars_relative_top_chain (hconn : IsConnected K.space)
    (c : Module.Dual (ZMod 2)
      (Tetrahedron K.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2))
    (hrelative : ∀ t : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      t.val.map (Function.Embedding.subtype _) ∉ L.faces →
        (triangleCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex).dualMap c
          (Pi.single t 1) = 0) :
    let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    let B : Triangle A → Prop := fun t =>
      t.val.map (Function.Embedding.subtype _) ∈ L.faces
    ∃ r : ZMod 2, c = r • totalTetrahedronChain A ∧
      (triangleCoboundary A).dualMap c = r • markedTriangleChain A B := by
  exact exists_scalar_total_of_relative_boundary _ _
    (original_chart_stars_tetrahedron_cofaces
      K hK L hLK hfull hN J F g hJF hg hLs hpure hstars)
    (original_chart_stars_tetrahedron_connected
      K hK L hLK hfull hN J F g hJF hg hLs hpure hstars hconn) c (by
        intro t ht
        apply Eq.trans _ (hrelative t ht)
        congr 1
        funext q
        by_cases hq : q = t
        · subst q
          simp
        · simp [hq])

open Classical in

theorem original_chart_stars_boundary3_injective (hconn : IsConnected K.space)
    (hfront : (frontier N).Nonempty) :
    Function.Injective
      (triangleCoboundary K.vertexAbstractComplex.toPreAbstractSimplicialComplex).dualMap := by
  classical
  have hboundary (z : G) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier N ↔ z ∈ L.space := by
    rw [hLs]
    exact PoincareConjecture.M76.original_model_mem_image_iff J F g hJF hg
      hN.frontier_subset ⟨z, hz⟩
  have hsurface := PoincareConjecture.M76.original_boundary_surface_incidence
    K L hK hLK hN.frontier_subset J g hg hboundary hstars
  obtain ⟨x, hx⟩ := hfront
  have hxL : F x ∈ L.space := hLs.symm ▸ mem_image_of_mem F hx
  obtain ⟨s, hs, _⟩ := SimplicialComplex.mem_space_iff.mp hxL
  obtain ⟨t, ht, _, htc⟩ := hsurface.1 s hs
  let tg : Triangle K.toPreAbstractSimplicialComplex := ⟨t, hLK ht, htc⟩
  let tv : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex :=
    (K.vertexFaceEquiv 3).symm tg
  have htv : tv.val.map (Function.Embedding.subtype _) ∈ L.faces := by
    rw [K.vertexFaceEquiv_symm_map]
    exact ht
  exact boundary3_injective_of_boundary_nonempty _ _
    (original_chart_stars_tetrahedron_cofaces
      K hK L hLK hfull hN J F g hJF hg hLs hpure hstars)
    (original_chart_stars_tetrahedron_connected
      K hK L hLK hfull hN J F g hJF hg hLs hpure hstars hconn) ⟨tv, htv⟩

end Geometry.OriginalPLTower
