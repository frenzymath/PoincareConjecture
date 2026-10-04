import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Polygons.ProtectedBoundaryTriangleModel
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.BoundaryEdgeLinkInterval
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Coordinates.OriginalChartConnectedLinks

/-!
# Complete boundary-edge intervals in the same protected model

The unchanged model supplies the whole original link and its exact
two old-boundary endpoints. All original triangle products and
whole marked carriers persist. See PrimeReduction009.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The same protected model constructs every complete boundary-edge
interval with the whole old-boundary link as its endpoint set. No
interval, endpoint or connectivity supplier is consumed.
See PrimeReduction009, sections2--5. -/
theorem exists_protected_boundary_edge_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (s → ℝ × V3) → R)
      (HB : (A 0).space ≃ₜ frontier R) (hK : K.faces.Finite),
      let : Fintype K.faces := hK.fintype
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      (∀ a, A a ≤ K ∧ (A a).faces.Finite ∧
        ∀ t ∈ K.faces, (∀ v ∈ t, v ∈ (A a).vertices) → t ∈ (A a).faces) ∧
      K.space = F '' R ∧ (A 0).space = F '' frontier R ∧
      (A 1).space = F '' D ∧ (A 2).space = F '' frontier D ∧
      (∀ x : R, (H x : s → ℝ × V3) = F x) ∧
      ContinuousOn g K.space ∧
      (∀ z : K.space, (g z : X) = (H.symm z : X)) ∧
      PolyhedralPLInCharts e (fun z => (g z : X)) K.space ∧
      (∀ t ∈ K.faces, ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4) ∧
      (∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
        MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
        (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y))) ∧
      (∀ t ∈ K.faces, t.card = 3 →
        (t ∈ (A 0).faces →
          {u | u ∈ K.faces ∧ u.card = 4 ∧ t ⊆ u}.ncard = 1) ∧
        (t ∉ (A 0).faces →
          {u | u ∈ K.faces ∧ u.card = 4 ∧ t ⊆ u}.ncard = 2)) ∧
      (∀ z : (A 0).space, (HB z : X) = (g z : X)) ∧
      (∀ t ∈ (A 0).faces, ∃ u ∈ (A 0).faces, t ⊆ u ∧ u.card = 3) ∧
      (∀ t ∈ (A 0).faces, t.card = 2 → ((A 0).faceLink t).vertices.ncard = 2) ∧
      (∀ p ∈ (A 0).vertices, IsConnected ((A 0).faceLink {p}).space) ∧
      (∀ t ∈ (A 0).faces, t.card = 3 →
        ∃ u ∈ K.faces, t ⊆ u ∧ u.card = 4 ∧
          ∃ J : Icc (0 : ℝ) 1 ≃ₜ (K.barycentricDualBlock t).space,
            J.IsFinitePL ∧
            (∀ x, (J x : s → ℝ × V3) =
              AffineMap.lineMap (t.centroid ℝ id) (u.centroid ℝ id) (x : ℝ)) ∧
            ∀ x, (J x : s → ℝ × V3) ∈ (A 0).space ↔ (x : ℝ) = 0) ∧
      ∀ t ∈ (A 0).faces, t.card = 2 →
        IsFinitePLBallPair ℝ (K.faceLink t).space ((A 0).faceLink t).space := by
  classical
  obtain ⟨s, F, K, A, H, g, HB, hK, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hpure, hstars, hfacets, hHB, hBpure, hBedge, hBconn, htriangle⟩ :=
    exists_protected_boundary_triangle_model hR he hDR b
  let : Fintype K.faces := hK.fintype
  have hboundary : ∀ z ∈ K.space, (g z : X) ∈ frontier R ↔ z ∈ (A 0).space := by
    intro z hz
    rw [hBs]
    exact original_model_mem_image_iff H F g hHF hg
      (frontier_subset_closure.trans he.closed.closure_subset) ⟨z, hz⟩
  have hlocal : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph X V3,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ R ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) := by
    intro p hp
    obtain ⟨B, hsource, _, hface, hregion⟩ := hstars p hp
    exact ⟨B, hsource, hface, hregion⟩
  have hcounts := original_chart_stars_facet_incidence K hK (A 0) (hA 0).1
    (hA 0).2.2 H g hg hboundary hpure hlocal
  have hlinks := original_chart_stars_connected_links K hK (A 0) (hA 0).1
    (hA 0).2.2 H g hg hboundary hlocal
  have hBcard : ∀ t ∈ (A 0).faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, hucard⟩ := hBpure t ht
    exact (Finset.card_le_card htu).trans (le_of_eq hucard)
  refine ⟨s, F, K, A, H, g, HB, hK, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hpure, hstars, hfacets, hHB, hBpure, hBedge, hBconn,
    htriangle, ?_⟩
  intro t ht htcard
  exact K.isFinitePLBallPair_boundary_edge_link (A 0) hK (hA 0).1 hpure hBcard
    hcounts ht htcard (hBedge t ht htcard)
    (hlinks t ((hA 0).1 ht) (by omega))

end PoincareMT.M76
