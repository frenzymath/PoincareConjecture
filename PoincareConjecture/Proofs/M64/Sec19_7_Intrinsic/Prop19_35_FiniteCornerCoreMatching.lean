import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapCoreMatching
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCoreMatching
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CoreContactRefinement









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture






theorem m64Intrinsic_refine_core_to_finite_corners_and_bands
    {I J : Type*} [Finite I] [Finite J]
    (H : J → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : J → ℝ)
    (face : J → Bool × Bool → SmoothFace AnnulusCoordinates) (positive : J → Bool)
    (C : J → Bool × Bool → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : J → Bool × Bool → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hC : ∀ e i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C e i) (C e i).source)
    (hCi : ∀ e i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C e i).symm (C e i).target)
    (hsource : ∀ e i, convexHull ℝ (range (b e i)) ⊆ (C e i).source)
    (hcarrier : ∀ e i, (face e i).carrier = C e i '' convexHull ℝ (range (b e i)))
    (hboundary : ∀ e i k, ((face e i).boundary k).map = C e i ∘
      affineChartSegment (b e i (k.succAbove 0)) (b e i (k.succAbove 1)))
    (hsub : ∀ e i, (face e i).carrier ⊆ H e '' ((H e).source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsecond : ∀ e i, ∀ t ∈ Icc (0 : ℝ) 1, ((face e i).boundary 1).map t =
      H e (sectorParameterEquiv 0 i (0, t * r e)))
    (hfirst : ∀ e i, ∀ t ∈ Icc (0 : ℝ) 1, ((face e i).boundary 2).map t =
      H e (sectorParameterEquiv 0 i (t * r e, 0)))
    (hchord : ∀ e i t, ((face e i).boundary 0).map t =
      (1 - t) • H e (sectorParameterEquiv 0 i (r e, 0)) +
        t • H e (sectorParameterEquiv 0 i (0, r e)))
    (L : I → AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates)
    (lo : I → ℝ → ℝ) (a d ua wa ub wb ra rb : I → ℝ)
    (B : ∀ i, ObliqueBandFaces (L i).toHomeomorph.toOpenPartialHomeomorph
      (lo i) (a i) (d i) (ua i) (wa i) (ub i) (wb i) (ra i) (rb i))
    {U K R : Set AnnulusCoordinates}
    (haxes : ∀ e, (fun t : ℝ => H e (0, t * r e)) '' Icc 0 1 ∪
      (fun t : ℝ => H e (t * r e, 0)) '' Icc 0 1 ⊆ K)
    (hcapremove : ∀ e, (⋃ i, ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
      (face e i).carrier) ⊆ R)
    (hbandremove : ∀ i, (B i).carrier ⊆ R)
    (hlower : ∀ i, (B i).lowerArc ⊆ K)
    (hcover : ∀ p ∈ closure U ∩ K, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R)
    (T : TriangleMesh) (hT : T.toPlaneComplex.support = closure (U \ R)) :
    ∃ S : TriangleMesh,
      S.toPlaneComplex.support = T.toPlaneComplex.support ∧
      S.toPlaneComplex.Subdivides T.toPlaneComplex ∧
      (∀ e i, (if positive e then i = (true, true) else i ≠ (true, true)) →
        ∀ t : S.Triangle, CoordinateTriangleBoundaryIntersection
          (OpenPartialHomeomorph.refl AnnulusCoordinates) (C e i) (meshTriangleBasis S t) (b e i)) ∧
      ∀ i (t : S.Triangle) (j : Fin (B i).interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
          ((B i).faceCoordinates j) (meshTriangleBasis S t) ((B i).faceBasis j) := by
  classical
  let _ := Fintype.ofFinite J
  obtain ⟨lines, _, hsupport, hband⟩ := m64Intrinsic_refine_core_to_linear_bands
    L lo a d ua wa ub wb ra rb B hbandremove hlower hcover T hT
  have hfinite (s : Finset J) : ∃ S : TriangleMesh,
      S.toPlaneComplex.support = T.toPlaneComplex.support ∧
      S.toPlaneComplex.Subdivides T.toPlaneComplex ∧
      (∀ e ∈ s, ∀ i, (if positive e then i = (true, true) else i ≠ (true, true)) →
        ∀ t : S.Triangle, CoordinateTriangleBoundaryIntersection
          (OpenPartialHomeomorph.refl AnnulusCoordinates) (C e i) (meshTriangleBasis S t) (b e i)) ∧
      ∀ i (t : S.Triangle) (j : Fin (B i).interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
          ((B i).faceCoordinates j) (meshTriangleBasis S t) ((B i).faceBasis j) := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨T.refineByLines lines, hsupport, T.refineByLines_subdivides lines,
        by simp, hband⟩
    | @insert e s _ ih =>
      obtain ⟨S, hS, hST, hcaps, hbands⟩ := ih
      obtain ⟨cuts, _, hsupport', hcap⟩ := m64Intrinsic_refine_core_to_retained_caps
        (H e) (r e) (face e) (positive e) (C e) (b e)
        (hC e) (hCi e) (hsource e) (hcarrier e) (hboundary e)
        (hsub e) (hsecond e) (hfirst e) (hchord e)
        (haxes e) (hcapremove e) hcover S (hS.trans hT)
      refine ⟨S.refineByLines cuts, hsupport'.trans hS,
        (S.refineByLines_subdivides cuts).trans hST, ?_, ?_⟩
      · intro f hf i hi
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact hcap i hi
        · exact m64Intrinsic_mesh_subdivision_preserves_boundary_contact
            (S.refineByLines_subdivides cuts) (C f i) (b f i) (hsource f i)
            (hcaps f hf i hi)
      · intro i t j
        exact m64Intrinsic_mesh_subdivision_preserves_boundary_contact
          (S.refineByLines_subdivides cuts) ((B i).faceCoordinates j) ((B i).faceBasis j)
          ((B i).face_triangle_subset_source j) (fun u => hbands i u j) t
  obtain ⟨S, hS, hST, hcaps, hbands⟩ := hfinite Finset.univ
  exact ⟨S, hS, hST, fun e => hcaps e (Finset.mem_univ e), hbands⟩

end PoincareConjecture
