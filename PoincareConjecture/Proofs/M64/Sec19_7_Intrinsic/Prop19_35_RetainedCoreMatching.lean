import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapCoreMatching
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandCoreMatching














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture







theorem m64Intrinsic_refine_core_to_retained_caps_and_bands
    {I : Type*} [Finite I]
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
    (face : Bool × Bool → SmoothFace AnnulusCoordinates) (positive : Bool)
    (C : Bool × Bool → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : Bool × Bool → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hC : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C i) (C i).source)
    (hCi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (C i).symm (C i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (C i).source)
    (hcarrier : ∀ i, (face i).carrier = C i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = C i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hsub : ∀ i, (face i).carrier ⊆ H '' (H.source ∩
      (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (hsecond : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 1).map t =
      H (sectorParameterEquiv 0 i (0, t * r)))
    (hfirst : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 2).map t =
      H (sectorParameterEquiv 0 i (t * r, 0)))
    (hchord : ∀ i t, ((face i).boundary 0).map t =
      (1 - t) • H (sectorParameterEquiv 0 i (r, 0)) +
        t • H (sectorParameterEquiv 0 i (0, r)))
    (L : I → AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates)
    (lo : I → ℝ → ℝ) (a d ua wa ub wb ra rb : I → ℝ)
    (B : ∀ i, ObliqueBandFaces (L i).toHomeomorph.toOpenPartialHomeomorph
      (lo i) (a i) (d i) (ua i) (wa i) (ub i) (wb i) (ra i) (rb i))
    {U K R : Set AnnulusCoordinates}
    (haxes : (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r, 0)) '' Icc 0 1 ⊆ K)
    (hcapremove : (⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      (face i).carrier) ⊆ R)
    (hbandremove : ∀ i, (B i).carrier ⊆ R)
    (hlower : ∀ i, (B i).lowerArc ⊆ K)
    (hcover : ∀ p ∈ closure U ∩ K, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R)
    (T : TriangleMesh) (hT : T.toPlaneComplex.support = closure (U \ R)) :
    ∃ S : TriangleMesh,
      S.toPlaneComplex.support = T.toPlaneComplex.support ∧
      S.toPlaneComplex.Subdivides T.toPlaneComplex ∧
      (∀ i, (if positive then i = (true, true) else i ≠ (true, true)) →
        ∀ t : S.Triangle, CoordinateTriangleBoundaryIntersection
          (OpenPartialHomeomorph.refl AnnulusCoordinates) (C i) (meshTriangleBasis S t) (b i)) ∧
      (∀ i (t : S.Triangle) (j : Fin (B i).interface.count × Bool),
        CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
            ((B i).faceCoordinates j) (meshTriangleBasis S t) ((B i).faceBasis j)) := by
  classical
  let _ := Fintype.ofFinite I
  choose cuts _ hcontact using fun i => m64Intrinsic_linear_band_core_cut_lines
    (L i) (B i) (hbandremove i) (hlower i) hcover
  let bandlines := (Finset.univ : Finset I).toList.flatMap cuts
  have hmem (i : I) {l : Plane →ᵃ[ℝ] ℝ} (hl : l ∈ cuts i) : l ∈ bandlines :=
    List.mem_flatMap.mpr ⟨i, by simp, hl⟩
  let T₁ := T.refineByLines bandlines
  have hT₁ : T₁.toPlaneComplex.support = closure (U \ R) :=
    (T.refineByLines_support bandlines).trans hT
  obtain ⟨caplines, _, hsupport, hcaps⟩ := m64Intrinsic_refine_core_to_retained_caps
    H r face positive C b hC hCi hsource hcarrier hboundary hsub hsecond hfirst hchord
    haxes hcapremove hcover T₁ hT₁
  refine ⟨T₁.refineByLines caplines,
    hsupport.trans (T.refineByLines_support bandlines),
    (T₁.refineByLines_subdivides caplines).trans (T.refineByLines_subdivides bandlines), hcaps, ?_⟩
  intro i
  apply hcontact i
  · rw [hsupport, hT₁]
  · intro l hl
    apply T₁.refineByLines_preserves_monochromatic caplines l
    exact T.refineByLines_isMonochromatic_of_mem bandlines (hmem i hl)

end PoincareConjecture
