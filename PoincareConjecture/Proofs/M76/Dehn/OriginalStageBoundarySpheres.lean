import PoincareConjecture.Proofs.M76.Dehn.OriginalStageBoundaryTrees
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComponentSurfaceSphere

set_option autoImplicit false

universe u v w z

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U : Type u} {G : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [DecidableEq G] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Stage.relative_region_boundary_spheres (st : Stage e S f r C)
    {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    {u : U} (hu : u ∈ S.space) (hfu : f u ∈ frontier R)
    (a : C(N, N))
    (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : range a = Subtype.val ⁻¹' (st.sourceMap '' S.space))
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    (A : SimplicialComplex ℝ G) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    (J : N ≃ₜ K.space) (F : st.Carrier → G) (g : G → N)
    (hJF : ∀ x : N, (J x : G) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (J.symm z : st.Carrier))
    (hAs : A.space = F '' frontier N)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)))
    (hterminal : ∀ (Y : Type (max w v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → st.Carrier),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
    ∃ L : (A.edgeComponentComplex c).space ≃ₜ frontier (TriangularRoofModel.halfBall 1),
      L.IsFinitePL := by
  classical
  have hA : A.faces.Finite := hK.subset hAK
  have hboundary (x : G) (hx : x ∈ K.space) :
      (g x : st.Carrier) ∈ frontier N ↔ x ∈ A.space := by
    rw [hAs]
    exact PoincareConjecture.M76.original_model_mem_image_iff J F g hJF hg
      hN.frontier_subset ⟨x, hx⟩
  obtain ⟨hpure, hcounts, hlinks⟩ := PoincareConjecture.M76.original_boundary_surface_incidence
    K A hK hAK hN.frontier_subset J g hg hboundary hstars
  obtain ⟨T, hT, hprimal, hdual⟩ := st.relative_region_boundary_trees
    hN hDN hNR hu hfu a H ha K hK A hAK hfull J F g hJF hg hAs hstars hterminal c
  apply A.exists_edgeComponent_sphere_model hA c hpure _ hlinks T hT hprimal hdual
  intro s hs hsc
  have hlink : (A.faceLink s).vertices.ncard =
      {t : Finset G | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard := by
    simpa only [hsc] using A.ncard_faceLink_vertices_eq_cofaces s
  exact hlink.symm.trans (hcounts s hs hsc)

end Geometry.OriginalPLTower
