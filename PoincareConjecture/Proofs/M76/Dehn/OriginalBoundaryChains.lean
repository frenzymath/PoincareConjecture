import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTetrahedronCofaces
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalFacetIncidence

set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

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

open Classical in

theorem original_chart_stars_tetrahedron_cofaces :
    ∀ t : Triangle K.vertexAbstractComplex.toPreAbstractSimplicialComplex,
      (tetrahedronCofaces K.vertexAbstractComplex.toPreAbstractSimplicialComplex t).card =
        if t.val.map (Function.Embedding.subtype _) ∈ L.faces then 1 else 2 := by
  classical
  have hboundary (z : G) (hz : z ∈ K.space) :
      (g z : X) ∈ frontier N ↔ z ∈ L.space := by
    rw [hLs]
    exact PoincareConjecture.M76.original_model_mem_image_iff J F g hJF hg
      hN.frontier_subset ⟨z, hz⟩
  have hinc := PoincareConjecture.M76.original_chart_stars_facet_incidence
    K hK L hLK hfull J g hg hboundary hpure hstars
  intro t
  let s : Finset G := t.val.map (Function.Embedding.subtype _)
  have hs : s ∈ K.faces := t.property.1
  have hsc : s.card = 3 := by
    dsimp only [s]
    rw [Finset.card_map]
    exact t.property.2
  have hcount : (K.faceLink s).vertices.ncard =
      {q : Finset G | q ∈ K.faces ∧ q.card = 4 ∧ s ⊆ q}.ncard := by
    simpa only [hsc] using K.ncard_faceLink_vertices_eq_cofaces s
  rw [K.tetrahedronCofaces_card_eq_original t]
  change {q : Finset G | q ∈ K.faces ∧ q.card = 4 ∧ s ⊆ q}.ncard =
    if s ∈ L.faces then 1 else 2
  rw [← hcount]
  by_cases h : s ∈ L.faces
  · rw [if_pos h]
    exact (hinc s hs hsc).1 h
  · rw [if_neg h]
    exact (hinc s hs hsc).2 h

open Classical in

theorem original_chart_stars_total_boundary :
    let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    let B : Triangle A → Prop := fun t =>
      t.val.map (Function.Embedding.subtype _) ∈ L.faces
    (triangleCoboundary A).dualMap (totalTetrahedronChain A) = markedTriangleChain A B ∧
      (edgeCoboundary A).dualMap (markedTriangleChain A B) = 0 := by
  classical
  have hcofaces := original_chart_stars_tetrahedron_cofaces
    K hK L hLK hfull hN J F g hJF hg hLs hpure hstars
  exact ⟨boundary3_total_eq_marked _ _ hcofaces, boundary2_marked_eq_zero _ _ hcofaces⟩

end Geometry.OriginalPLTower
