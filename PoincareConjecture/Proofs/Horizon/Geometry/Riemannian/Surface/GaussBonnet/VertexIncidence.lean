import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.VertexContributions
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.EdgeGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

theorem coordinate_corner_in_face_is_corner {I : Type*}
    (face : I → SmoothFace S) (F : I → OpenPartialHomeomorph Plane S)
    (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (i j : I) (v : Fin 3) (hqj : F i (b i v) ∈ (face j).carrier) :
    ∃ k : Fin 3, F j (b j k) = F i (b i v) := by
  by_cases hji : j = i
  · subst j
    exact ⟨v, rfl⟩
  have hqi : F i (b i v) ∈ (face i).carrier := by
    rw [hcarrier i]
    exact mem_image_of_mem (F i) (subset_convexHull ℝ _ (mem_range_self v))
  rcases hinter j i hji with ⟨k, l, hmeet, hedge⟩ | ⟨w, hw⟩
  · have hqedge : F i (b i v) ∈ ((face i).boundary l).map '' Icc (0 : ℝ) 1 := by
      rw [← hedge, ← hmeet]
      exact ⟨hqj, hqi⟩
    obtain ⟨t, ht, htq⟩ := hqedge
    have hparam := htq
    rw [hboundary i l] at hparam
    have hends := Euler.equal_coordinate_edge_endpoints_mem (F j) (b j) (hsource j)
      k ((face i).boundary l) (hinj i l) (by rw [← hboundary j k]; exact hedge.symm)
    have hqends : F i (b i v) ∈
        ({F j (b j (k.succAbove 0)), F j (b j (k.succAbove 1))} : Set S) := by
      rcases Euler.coordinate_vertex_on_edge (F i) (b i) (hsource i) l v ht hparam with h0 | h1
      · rw [h0] at htq
        exact htq ▸ hends.1
      · rw [h1] at htq
        exact htq ▸ hends.2
    rcases hqends with h0 | h1
    · exact ⟨k.succAbove 0, h0.symm⟩
    · exact ⟨k.succAbove 1, (mem_singleton_iff.mp h1).symm⟩
  · exact ⟨w, (mem_singleton_iff.mp (hw ⟨hqj, hqi⟩)).symm⟩

theorem coordinate_vertex_mem_face_iff {I : Type*}
    (face : I → SmoothFace S) (F : I → OpenPartialHomeomorph Plane S)
    (b : I → AffineBasis (Fin 3) ℝ Plane)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
    (q : Euler.CoordinateVertex F b) (j : I) :
    q.1 ∈ (face j).carrier ↔ ∃! k : Fin 3, F j (b j k) = q.1 := by
  constructor
  · intro hq
    obtain ⟨⟨i, v⟩, hv⟩ := q.2
    change F i (b i v) = q.1 at hv
    have hq' : F i (b i v) ∈ (face j).carrier := hv.symm ▸ hq
    obtain ⟨k, hk⟩ := coordinate_corner_in_face_is_corner face F b
      hsource hcarrier hboundary hinj hinter i j v hq'
    refine ⟨k, hk.trans hv, ?_⟩
    intro l hl
    apply (b j).ind.injective
    exact (F j).injOn (hsource j (subset_convexHull ℝ _ (mem_range_self l)))
      (hsource j (subset_convexHull ℝ _ (mem_range_self k))) (hl.trans (hk.trans hv).symm)
  · rintro ⟨k, hk, _⟩
    rw [hcarrier j, ← hk]
    exact mem_image_of_mem (F j) (subset_convexHull ℝ _ (mem_range_self k))

end PoincareConjecture.Topology.Surface
