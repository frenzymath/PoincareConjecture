import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.ProtectedBoundaryEdgeModel
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.BoundaryEdgeDualMarks

/-!
# Complete marked boundary-edge disks in the same protected model

Every disk, both full rim arcs and the two prescribed triangle
intervals use the original K, boundary mark, inverse and chart stars.
No disk, collar or incidence supplier is introduced. See Prime010.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- Construct every complete original boundary-edge disk and its
marked rim from the protected input, retaining all previous original
triangle products and full carriers. See Prime010, sections1--5. -/
theorem exists_protected_boundary_dual_disk_model
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R D : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) :
    ∃ (s : Finset R) (F : X → (s → ℝ × V3))
      (K : SimplicialComplex ℝ (s → ℝ × V3))
      (A : Fin 3 → SimplicialComplex ℝ (s → ℝ × V3))
      (H : R ≃ₜ K.space) (g : (s → ℝ × V3) → R)
      (HB : (A 0).space ≃ₜ frontier R) (hK : K.faces.Finite)
      (hL : (A 0).faces.Finite),
      let : Fintype K.faces := hK.fintype
      let : Fintype (A 0).faces := hL.fintype
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
      (∀ t ∈ (A 0).faces, t.card = 2 →
        IsFinitePLBallPair ℝ (K.faceLink t).space ((A 0).faceLink t).space) ∧
      ∀ t ∈ (A 0).faces, t.card = 2 →
        IsFinitePLBallPair (ℝ × ℝ) (K.barycentricDualBlock t).space
          (((K.barycentricDualBlock t).link (t.centroid ℝ id)).space ∪
            ((A 0).barycentricDualBlock t).space) ∧
        (K.barycentricDualBlock t).space ∩ (A 0).space =
          ((A 0).barycentricDualBlock t).space ∧
        ∃ v w : Finset (s → ℝ × V3), v ∈ (A 0).faces ∧ w ∈ (A 0).faces ∧
          v.card = 3 ∧ w.card = 3 ∧ t ⊆ v ∧ t ⊆ w ∧ v ≠ w ∧
          (∀ z ∈ (A 0).faces, t ⊆ z → z.card = 3 → z = v ∨ z = w) ∧
          IsFinitePLBallPair ℝ ((K.barycentricDualBlock t).link (t.centroid ℝ id)).space
            {v.centroid ℝ id, w.centroid ℝ id} ∧
          IsFinitePLBallPair ℝ ((A 0).barycentricDualBlock t).space
            {v.centroid ℝ id, w.centroid ℝ id} ∧
          ((A 0).barycentricDualBlock t).space =
            segment ℝ (t.centroid ℝ id) (v.centroid ℝ id) ∪
              segment ℝ (t.centroid ℝ id) (w.centroid ℝ id) ∧
          ((K.barycentricDualBlock t).link (t.centroid ℝ id)).space ∩
              ((A 0).barycentricDualBlock t).space =
            {v.centroid ℝ id, w.centroid ℝ id} ∧
          (K.barycentricDualBlock v).space ⊆
            ((K.barycentricDualBlock t).link (t.centroid ℝ id)).space ∧
          (K.barycentricDualBlock w).space ⊆
            ((K.barycentricDualBlock t).link (t.centroid ℝ id)).space ∧
          (K.barycentricDualBlock v).space ∩ ((A 0).barycentricDualBlock t).space =
            {v.centroid ℝ id} ∧
          (K.barycentricDualBlock w).space ∩ ((A 0).barycentricDualBlock t).space =
            {w.centroid ℝ id} ∧
          Disjoint (K.barycentricDualBlock v).space (K.barycentricDualBlock w).space := by
  classical
  obtain ⟨s, F, K, A, H, g, HB, hK, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hpure, hstars, hfacets, hHB, hBpure, hBedge, hBconn,
    htriangle, hedge⟩ := exists_protected_boundary_edge_model hR he hDR b
  let : Fintype K.faces := hK.fintype
  let hL := (hA 0).2.1
  let : Fintype (A 0).faces := hL.fintype
  have hBcard : ∀ t ∈ (A 0).faces, t.card ≤ 3 := by
    intro t ht
    obtain ⟨u, _, htu, huc⟩ := hBpure t ht
    exact (Finset.card_le_card htu).trans (le_of_eq huc)
  refine ⟨s, F, K, A, H, g, HB, hK, hL, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hpure, hstars, hfacets, hHB, hBpure, hBedge, hBconn,
    htriangle, hedge, ?_⟩
  intro t ht htc
  exact K.exists_boundary_edge_dual_marks (A 0) (hA 0).1 hBcard (hA 0).2.2
    ht htc (hBedge t ht htc) (hedge t ht htc)

end PoincareMT.M76
