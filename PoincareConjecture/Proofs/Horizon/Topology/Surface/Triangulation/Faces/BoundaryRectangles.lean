


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.BoundaryRectangles
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Rectangles








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable {D : FiniteChartRegionDecomposition (M := M)}

namespace BoundaryRectangle

variable {a : D.EdgeIndex} (R : D.BoundaryRectangle a)


noncomputable def triangleBasis : Bool → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))
  | false => rectangleLowerBasis (c := -R.width / 2) (d := R.width / 2)
      R.left_lt_right (by linarith [R.width_pos])
  | true => rectangleUpperBasis (c := -R.width / 2) (d := R.width / 2)
      R.left_lt_right (by linarith [R.width_pos])

omit [T2Space M] in
theorem triangle_sources_cover :
    convexHull ℝ (range (R.triangleBasis false)) ∪
      convexHull ℝ (range (R.triangleBasis true)) = R.closedSource :=
  rectangle_triangle_union R.left_lt_right
    (show -R.width / 2 < R.width / 2 by linarith [R.width_pos])

omit [T2Space M] in
theorem triangle_subset (i : Bool) :
    convexHull ℝ (range (R.triangleBasis i)) ⊆ R.closedSource := by
  rw [← R.triangle_sources_cover]
  cases i
  · exact subset_union_left
  · exact subset_union_right

private theorem segment_image (x y : EuclideanSpace ℝ (Fin 2)) :
    affineChartSegment x y '' Icc (0 : ℝ) 1 = affineSegment ℝ x y := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]



theorem exists_smoothFaces :
    ∃ face : Bool → SmoothFace M,
      (∀ i, (face i).map = R.coordinates) ∧
      (∀ i, (face i).source = convexHull ℝ (range (R.triangleBasis i))) ∧
      (∀ i, (face i).carrier = R.coordinates '' convexHull ℝ (range (R.triangleBasis i))) ∧
      (∀ i, InjOn (face i).map (face i).source) ∧
      (∀ i k, ((face i).boundary k).map = R.coordinates ∘
        affineChartSegment (R.triangleBasis i (k.succAbove 0))
          (R.triangleBasis i (k.succAbove 1))) ∧
      (∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1)) ∧
      (face false).carrier ∪ (face true).carrier = R.carrier ∧
      (face false).carrier ∩ (face true).carrier =
        ((face false).boundary 1).map '' Icc (0 : ℝ) 1 ∧
      (face false).boundary 1 = (face true).boundary 1 := by
  have htriangle (i : Bool) :
      convexHull ℝ (range (R.triangleBasis i)) ⊆ R.coordinates.source :=
    (R.triangle_subset i).trans R.closedSource_subset
  choose face hmap hsource hcarrier hinj hboundary using fun i =>
    exists_smoothFace_of_smooth_coordinates R.coordinates R.smooth R.smooth_symm
      (R.triangleBasis i) (htriangle i) (a.1.1 : M)
      ((image_mono (R.triangle_subset i)).trans R.carrier_subset_chart)
  refine ⟨face, hmap, hsource, hcarrier, hinj, hboundary, ?_, ?_, ?_, ?_⟩
  · intro i k u hu v hv huv
    let x := R.triangleBasis i (k.succAbove 0)
    let y := R.triangleBasis i (k.succAbove 1)
    have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        affineChartSegment x y t ∈ R.coordinates.source := by
      apply htriangle i
      apply segment_subset_convexHull (mem_range_self (k.succAbove 0))
        (mem_range_self (k.succAbove 1))
      rw [← affineSegment_eq_segment, ← segment_image]
      exact mem_image_of_mem _ ht
    have hxy : y - x ≠ 0 := by
      intro h
      have he := (R.triangleBasis i).ind.injective (sub_eq_zero.mp h)
      have h10 : (1 : Fin 2) = 0 := Fin.succAbove_right_injective he
      norm_num at h10
    rw [hboundary i k] at huv
    have heq := R.coordinates.injOn (hseg u hu) (hseg v hv) huv
    exact smul_left_injective ℝ hxy (add_left_cancel heq)
  · rw [hcarrier, hcarrier, ← image_union, R.triangle_sources_cover]
    rfl
  · rw [hcarrier, hcarrier,
      ← R.coordinates.injOn.image_inter (htriangle false) (htriangle true)]
    rw [show convexHull ℝ (range (R.triangleBasis false)) ∩
        convexHull ℝ (range (R.triangleBasis true)) =
        affineSegment ℝ (!₂[R.left, -R.width / 2] : EuclideanSpace ℝ (Fin 2))
          !₂[R.right, R.width / 2] from
        rectangle_triangle_inter R.left_lt_right
          (show -R.width / 2 < R.width / 2 by linarith [R.width_pos]), hboundary]
    change R.coordinates '' affineSegment ℝ
      (!₂[R.left, -R.width / 2] : EuclideanSpace ℝ (Fin 2)) !₂[R.right, R.width / 2] =
      (R.coordinates ∘ affineChartSegment !₂[R.left, -R.width / 2]
        !₂[R.right, R.width / 2]) '' Icc (0 : ℝ) 1
    rw [← segment_image, image_image]
    rfl
  · have heq : ((face false).boundary 1).map = ((face true).boundary 1).map := by
      rw [hboundary, hboundary]
      rfl
    cases h₀ : (face false).boundary 1 with
    | mk m sm reg =>
      cases h₁ : (face true).boundary 1 with
      | mk m' sm' reg' =>
        simp only [h₀, h₁] at heq
        cases heq
        rfl

end BoundaryRectangle




theorem exists_boundary_rectangle_faces (D : FiniteChartRegionDecomposition (M := M))
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius p) :
    ∃ (R : ∀ a : D.EdgeIndex, D.BoundaryRectangle a)
      (face : D.EdgeIndex → Bool → SmoothFace M),
      (∀ a i, (face a i).map = (R a).coordinates) ∧
      (∀ a i, (face a i).source = convexHull ℝ (range ((R a).triangleBasis i))) ∧
      (∀ a i, (face a i).carrier = (R a).coordinates ''
        convexHull ℝ (range ((R a).triangleBasis i))) ∧
      (∀ a i, InjOn (face a i).map (face a i).source) ∧
      (∀ a i k, ((face a i).boundary k).map = (R a).coordinates ∘
        affineChartSegment ((R a).triangleBasis i (k.succAbove 0))
          ((R a).triangleBasis i (k.succAbove 1))) ∧
      (∀ a i k, InjOn ((face a i).boundary k).map (Icc (0 : ℝ) 1)) ∧
      (∀ a, (face a false).carrier ∪ (face a true).carrier = (R a).carrier) ∧
      (∀ a, (face a false).carrier ∩ (face a true).carrier =
        ((face a false).boundary 1).map '' Icc (0 : ℝ) 1) ∧
      (∀ a, (face a false).boundary 1 = (face a true).boundary 1) ∧
      (∀ a b, a ≠ b → ∀ i j, Disjoint (face a i).carrier (face b j).carrier) ∧
      (∀ a i, (face a i).carrier ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).source) ∧
      chartDiskBoundaryUnion D.centers D.radius ⊆
        (⋃ p, (P p).openCarrier) ∪ (⋃ a, (R a).openCarrier) ∧
      chartDiskBoundaryUnion D.centers D.radius ⊆
        (⋃ p, (P p).carrier) ∪ (⋃ a, ⋃ i, (face a i).carrier) := by
  obtain ⟨R, _, hdis, _, hcover⟩ := D.exists_boundary_rectangles P
  choose face hmap hsource hcarrier hinj hboundary hedgeinj hunion hinter hedge using
    fun a => (R a).exists_smoothFaces
  have hsub (a : D.EdgeIndex) (i : Bool) : (face a i).carrier ⊆ (R a).carrier := by
    rw [hcarrier]
    exact image_mono ((R a).triangle_subset i)
  refine ⟨R, face, hmap, hsource, hcarrier, hinj, hboundary, hedgeinj, hunion, hinter,
    hedge, ?_, ?_, hcover, ?_⟩
  · intro a b hab i j
    exact (hdis hab).mono (hsub a i) (hsub b j)
  · intro a i
    exact (hsub a i).trans (R a).carrier_subset_chart
  · intro z hz
    rcases hcover hz with hp | hr
    · obtain ⟨p, hp⟩ := mem_iUnion.mp hp
      exact Or.inl (mem_iUnion.mpr ⟨p, (P p).openCarrier_subset_carrier hp⟩)
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hr
      have hza := (R a).openCarrier_subset_carrier ha
      rw [← hunion a] at hza
      rcases hza with hza | hza
      · exact Or.inr (mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨false, hza⟩⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨true, hza⟩⟩)

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
