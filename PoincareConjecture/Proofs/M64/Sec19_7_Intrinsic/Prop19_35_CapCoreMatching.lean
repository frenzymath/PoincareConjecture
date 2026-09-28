import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ExposedCapChords
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Meshes.ConnectedIntersections
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Meshes.BoundaryContact















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface Poincare.Topology.Plane.Meshes
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

open Classical in






theorem m64Intrinsic_refine_core_to_retained_caps
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
    {U K R : Set AnnulusCoordinates}
    (haxes : (fun t : ℝ => H (0, t * r)) '' Icc 0 1 ∪
      (fun t : ℝ => H (t * r, 0)) '' Icc 0 1 ⊆ K)
    (hremove : (⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      (face i).carrier) ⊆ R)
    (hcover : ∀ p ∈ closure U ∩ K, ∃ W : Set AnnulusCoordinates,
      IsOpen W ∧ p ∈ W ∧ W ∩ closure U ⊆ R)
    (T : TriangleMesh) (hT : T.toPlaneComplex.support = closure (U \ R)) :
    ∃ lines : List (Plane →ᵃ[ℝ] ℝ),
      (∀ l ∈ lines, Function.Surjective l) ∧
      (T.refineByLines lines).toPlaneComplex.support = T.toPlaneComplex.support ∧
      ∀ i, (if positive then i = (true, true) else i ≠ (true, true)) →
        ∀ t : (T.refineByLines lines).Triangle,
          CoordinateTriangleBoundaryIntersection (OpenPartialHomeomorph.refl AnnulusCoordinates)
            (C i) (meshTriangleBasis (T.refineByLines lines) t) (b i) := by
  let p (i : Bool × Bool) := H (sectorParameterEquiv 0 i (r, 0))
  let q (i : Bool × Bool) := H (sectorParameterEquiv 0 i (0, r))
  have hchordset (i : Bool × Bool) :
      ((face i).boundary 0).map '' Icc (0 : ℝ) 1 = segment ℝ (p i) (q i) := by
    rw [segment_eq_image]
    exact image_congr (fun t _ => hchord i t)
  choose l hsurj hline using fun i : Bool × Bool =>
    Poincare.Topology.Plane.exists_affine_line_containing_segment (p i) (q i)
  let lines := (Finset.univ : Finset (Bool × Bool)).toList.map l
  have hmem (i : Bool × Bool) : l i ∈ lines := List.mem_map.mpr ⟨i, by simp, rfl⟩
  have hcontact := m64Intrinsic_residual_core_cap_chord H r face positive
    hsub hsecond hfirst hchord
    (fun i => ⟨C i, b i, hC i, hCi i, hsource i, hcarrier i, hboundary i⟩)
    haxes hremove hcover
  refine ⟨lines, ?_, T.refineByLines_support lines, ?_⟩
  · intro k hk
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
    exact hsurj i
  intro i hi t
  let S := T.refineByLines lines
  let A := convexHull ℝ (range (meshTriangleBasis S t))
  let chord := segment ℝ (p i) (q i)
  have hAT : A ⊆ closure (U \ R) := by
    have h := meshTriangleBasis_subset_support S t
    rw [T.refineByLines_support, hT] at h
    exact h
  have hbound : A ∩ (face i).carrier ⊆ chord := by
    dsimp only [chord]
    rw [← hchordset]
    exact (inter_subset_inter_left _ hAT).trans (hcontact i hi)
  have hchordcap : chord ⊆ (face i).carrier := by
    dsimp only [chord]
    rw [← hchordset]
    exact ((face i).boundary_image_subset_frontier 0).trans
      (face i).isClosed_carrier.frontier_subset
  have heq : A ∩ (face i).carrier = A ∩ chord := by
    apply Subset.antisymm
    · exact fun z hz => ⟨hz.1, hbound hz⟩
    · exact fun z hz => ⟨hz.1, hchordcap hz.2⟩
  have hmono := T.refineByLines_isMonochromatic_of_mem lines (hmem i)
  have hside : (∀ k, 0 ≤ l i (meshTriangleBasis S t k)) ∨
      (∀ k, l i (meshTriangleBasis S t k) ≤ 0) := by
    have hvertices (k : Fin 3) : meshTriangleBasis S t k ∈ S.triangleCarrier t.1 := by
      change _ ∈ convexHull ℝ (S.position '' (t.1 : Set S.Vertex))
      rw [← range_meshTriangleBasis]
      exact subset_convexHull ℝ _ (mem_range_self _)
    rcases hmono.triangleCarrier_halfspace S t with hpos | hneg
    · exact Or.inl (fun k => hpos _ (hvertices k))
    · exact Or.inr (fun k => hneg _ (hvertices k))
  apply CoordinateTriangleBoundaryIntersection.of_convex_chart_contact
    (OpenPartialHomeomorph.refl AnnulusCoordinates) (C i) (meshTriangleBasis S t) (b i)
    (subset_univ _) (hsource i) chord (convex_segment _ _) ?_ (l i) (hsurj i)
    hside (hline i) 0 ?_
  · simpa only [OpenPartialHomeomorph.refl_apply, image_id, ← hcarrier] using heq
  · simp only [OpenPartialHomeomorph.refl_apply, image_id, ← hcarrier]
    apply hbound.trans
    dsimp only [chord]
    rw [← hchordset, hboundary]
    rw [image_comp]
    apply image_mono
    unfold affineSegment
    apply subset_of_eq
    congr 1
    funext u
    simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]

end PoincareConjecture
