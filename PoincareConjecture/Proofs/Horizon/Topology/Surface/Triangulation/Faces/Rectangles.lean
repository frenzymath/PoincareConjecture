


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Triangles.Rectangle








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]



theorem exists_smoothFace_pair_of_coordinate_rectangle_with_boundaries
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} ⊆ F.source)
    (p : M) (hchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ∃ f g : SmoothFace M,
      f.map = F ∧ g.map = F ∧
      f.source = convexHull ℝ (range (rectangleLowerBasis hab hcd)) ∧
      g.source = convexHull ℝ (range (rectangleUpperBasis hab hcd)) ∧
      InjOn f.map f.source ∧ InjOn g.map g.source ∧
      f.carrier ∪ g.carrier =
        F '' {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} ∧
      f.carrier ∩ g.carrier = (f.boundary 1).map '' Icc (0 : ℝ) 1 ∧
      f.boundary 1 = g.boundary 1 ∧
      (∀ t : ℝ, (f.boundary 2).map t = F !₂[a + t * (b - a), c]) ∧
      (∀ i, (f.boundary i).map = F ∘ affineChartSegment
        (rectangleLowerBasis hab hcd (i.succAbove 0))
        (rectangleLowerBasis hab hcd (i.succAbove 1))) ∧
      (∀ i, (g.boundary i).map = F ∘ affineChartSegment
        (rectangleUpperBasis hab hcd (i.succAbove 0))
        (rectangleUpperBasis hab hcd (i.succAbove 1))) := by
  have hsub₀ : convexHull ℝ (range (rectangleLowerBasis hab hcd)) ⊆ F.source := by
    apply Subset.trans subset_union_left
    rw [rectangle_triangle_union hab hcd]
    exact hrect
  have hsub₁ : convexHull ℝ (range (rectangleUpperBasis hab hcd)) ⊆ F.source := by
    apply Subset.trans subset_union_right
    rw [rectangle_triangle_union hab hcd]
    exact hrect
  obtain ⟨f, hfmap, hfsource, hfcarrier, hfinj, hfedge⟩ :=
    exists_smoothFace_of_smooth_coordinates F hF hFinv
      (rectangleLowerBasis hab hcd) hsub₀ p
      (fun _ ⟨z, hz, hzy⟩ => hzy ▸ hchart (F.map_source (hsub₀ hz)))
  obtain ⟨g, hgmap, hgsource, hgcarrier, hginj, hgedge⟩ :=
    exists_smoothFace_of_smooth_coordinates F hF hFinv
      (rectangleUpperBasis hab hcd) hsub₁ p
      (fun _ ⟨z, hz, hzy⟩ => hzy ▸ hchart (F.map_source (hsub₁ hz)))
  refine ⟨f, g, hfmap, hgmap, hfsource, hgsource, hfinj, hginj, ?_, ?_, ?_, ?_,
    hfedge, hgedge⟩
  · rw [hfcarrier, hgcarrier, ← image_union, rectangle_triangle_union hab hcd]
  · rw [hfcarrier, hgcarrier, ← F.injOn.image_inter hsub₀ hsub₁,
      rectangle_triangle_inter hab hcd, hfedge 1]
    change F '' affineSegment ℝ (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d] =
      (F ∘ affineChartSegment !₂[a, c] !₂[b, d]) '' Icc (0 : ℝ) 1
    have hseg : affineChartSegment (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d] ''
        Icc (0 : ℝ) 1 = affineSegment ℝ (!₂[a, c] : EuclideanSpace ℝ (Fin 2)) !₂[b, d] := by
      unfold affineSegment
      congr 1
      funext t
      simp [affineChartSegment, AffineMap.lineMap_apply, add_comm]
    rw [← hseg, image_image]
    rfl
  · have hmap : (f.boundary 1).map = (g.boundary 1).map := by
      rw [hfedge 1, hgedge 1]
      rfl
    cases h₀ : f.boundary 1 with
    | mk m sm reg =>
      cases h₁ : g.boundary 1 with
      | mk m' sm' reg' =>
        simp only [h₀, h₁] at hmap
        cases hmap
        rfl
  · intro t
    rw [hfedge 2]
    change F (affineChartSegment !₂[a, c] !₂[b, c] t) = F !₂[a + t * (b - a), c]
    congr 1
    ext i
    fin_cases i <;> simp [affineChartSegment]


theorem exists_smoothFace_pair_of_coordinate_rectangle
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} ⊆ F.source)
    (p : M) (hchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ∃ f g : SmoothFace M,
      f.map = F ∧ g.map = F ∧
      f.source = convexHull ℝ (range (rectangleLowerBasis hab hcd)) ∧
      g.source = convexHull ℝ (range (rectangleUpperBasis hab hcd)) ∧
      InjOn f.map f.source ∧ InjOn g.map g.source ∧
      f.carrier ∪ g.carrier =
        F '' {z : EuclideanSpace ℝ (Fin 2) | z 0 ∈ Icc a b ∧ z 1 ∈ Icc c d} ∧
      f.carrier ∩ g.carrier = (f.boundary 1).map '' Icc (0 : ℝ) 1 ∧
      f.boundary 1 = g.boundary 1 ∧
      (∀ t : ℝ, (f.boundary 2).map t = F !₂[a + t * (b - a), c]) := by
  obtain ⟨f, g, hf, hg, hfs, hgs, hfi, hgi, hcover, hinter, hdiag, hlower, _, _⟩ :=
    exists_smoothFace_pair_of_coordinate_rectangle_with_boundaries F hF hFinv hab hcd
      hrect p hchart
  exact ⟨f, g, hf, hg, hfs, hgs, hfi, hgi, hcover, hinter, hdiag, hlower⟩

end PoincareConjecture.Topology.Surface
