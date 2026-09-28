import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedBoundaryEdgeProducts
import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryVertexHalfBall

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_protected_boundary_vertex_model
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
      ∃ T : SimplicialComplex.BoundaryTriangleFibers K (A 0),
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
      (∀ t ∈ (A 0).faces, t.card = 2 →
        IsFinitePLBallPair ℝ (K.faceLink t).space ((A 0).faceLink t).space) ∧
      (∀ t ∈ (A 0).faces, t.card = 2 → ∃ P : (s → ℝ × V3) × ℝ → (s → ℝ × V3),
        FinitePiecewiseAffineOn P (((A 0).barycentricDualBlock t).space ×ˢ I) ∧
        InjOn P (((A 0).barycentricDualBlock t).space ×ˢ I) ∧
        P '' (((A 0).barycentricDualBlock t).space ×ˢ I) = (K.barycentricDualBlock t).space ∧
        (∀ x ∈ ((A 0).barycentricDualBlock t).space, P (x, 0) = x) ∧
        (∀ u ∈ (A 0).faces, t ⊆ u → u.card = 3 → ∀ r ∈ I,
          P (u.centroid ℝ id, r) = T.map u r) ∧
        (∀ x ∈ ((A 0).barycentricDualBlock t).space ×ˢ I,
          P x ∈ (A 0).space ↔ x.2 = 0) ∧
        ∀ x ∈ ((A 0).barycentricDualBlock t).space ×ˢ I,
          P x ∈ ((K.barycentricDualBlock t).link (t.centroid ℝ id)).space ↔
            x.1 ∈ ((A 0).barycentricDualBlock t).space ∩
              ((K.barycentricDualBlock t).link (t.centroid ℝ id)).space ∨ x.2 = 1) ∧
      ∀ p ∈ (A 0).vertices,
        Nonempty (SimplicialComplex.BoundaryVertexHalfBall K (A 0) p) := by
  classical
  obtain ⟨s, F, K, A, H, g, HB, hK, hL, T, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hpure, hstars, hfacets, hHB, hBpure, hBedge, hBconn,
    hedge, hproducts⟩ := exists_protected_boundary_edge_products hR he hDR b
  let : Fintype K.faces := hK.fintype
  let : Fintype (A 0).faces := hL.fintype
  refine ⟨s, F, K, A, H, g, HB, hK, hL, T, hFc, hF, hA, hKs, hBs, hDs, hSs,
    hHF, hgc, hg, hgPL, hpure, hstars, hfacets, hHB, hBpure, hBedge, hBconn,
    hedge, hproducts, ?_⟩
  intro p hp
  obtain ⟨B, hsource, _, hface, hregion⟩ := hstars p ((hA 0).1 hp)
  exact K.exists_boundary_vertex_half_ball (A 0) (hA 0).1 H g hg HB hHB
    hp B hsource hface hregion

end PoincareConjecture.M76
