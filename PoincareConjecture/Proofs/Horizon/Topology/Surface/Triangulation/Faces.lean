


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartTriangles
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Planar











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

private theorem affineChartSegment_image (a b : EuclideanSpace ℝ (Fin 2)) :
    affineChartSegment a b '' Icc (0 : ℝ) 1 = affineSegment ℝ a b := by
  unfold affineSegment
  congr 1
  funext t
  simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]



theorem exists_smoothFace_of_chart_triangle (x : M)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : convexHull ℝ (range b) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    ∃ f : SmoothFace M,
      f.map = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ∧
      f.source = convexHull ℝ (range b) ∧
      f.carrier = (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        convexHull ℝ (range b) ∧
      Set.InjOn f.map f.source := by
  classical
  have hseg (i : Fin 3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      affineChartSegment (b (i.succAbove 0)) (b (i.succAbove 1)) t ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target := by
    apply hsub
    apply segment_subset_convexHull (mem_range_self (i.succAbove 0))
      (mem_range_self (i.succAbove 1))
    rw [← affineSegment_eq_segment, ← affineChartSegment_image]
    exact mem_image_of_mem _ ht
  have hne (i : Fin 3) : b (i.succAbove 0) ≠ b (i.succAbove 1) := by
    intro h
    have hi : (0 : Fin 2) = 1 :=
      (Fin.succAbove_right_injective (p := i)) (b.ind.injective h)
    norm_num at hi
  choose edge hedge hinj hstart hend using fun i : Fin 3 =>
    exists_smoothEdge_of_affineChartSegment x (hne i) (hseg i)
  let f : SmoothFace M := {
    map := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm
    source := convexHull ℝ (range b)
    source_compact := (finite_range b).isCompact_convexHull ℝ
    source_triangle := by
      refine ⟨b 0, b 1, b 2, ?_⟩
      congr 1
      ext y
      simp only [mem_range, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
    smooth := (contMDiffOn_chart_symm (I := 𝓡 2) (x := x)).mono hsub
    carrier := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm '' convexHull ℝ (range b)
    carrier_eq_image := rfl
    chart := x
    carrier_subset_chart := by
      rintro _ ⟨z, hz, rfl⟩
      exact (chartAt (EuclideanSpace ℝ (Fin 2)) x).map_target (hsub hz)
    boundary := edge
    boundary_carrier := by
      rw [frontier_chart_image x ((finite_range b).isCompact_convexHull ℝ) hsub,
        frontier_convexHull_affineBasis_fin3_segments, image_iUnion]
      congr 1
      funext i
      rw [hedge i, ← affineChartSegment_image, image_image]
      rfl }
  exact ⟨f, rfl, rfl, rfl,
    (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm.injOn.mono hsub⟩




theorem exists_finite_smoothFace_cover [CompactSpace M] :
    ∃ (s : Finset M) (face : M → SmoothFace M),
      (⋃ x ∈ s, interior (face x).carrier) = (univ : Set M) := by
  obtain ⟨s, b, hcenter, hsub, hcover⟩ := exists_finite_chart_triangle_cover (M := M)
  choose face hmap hsource hcarrier hinj using fun x : M =>
    exists_smoothFace_of_chart_triangle x (b x) (hsub x)
  refine ⟨s, face, ?_⟩
  rw [show (⋃ x ∈ s, interior (face x).carrier) =
      ⋃ x ∈ s, interior ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        convexHull ℝ (range (b x))) by
    apply iUnion_congr
    intro x
    apply iUnion_congr
    intro hx
    rw [hcarrier x]]
  exact hcover

end PoincareConjecture.Topology.Surface
