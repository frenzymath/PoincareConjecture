import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Coordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]

omit [T2Space M] in

theorem interior_smooth_coordinate_image
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : K ⊆ F.source) :
    interior (F '' K) = F '' interior K := by
  have himage : F '' K ⊆ F.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact F.map_source (hK hz)
  have himage_eq : F.IsImage K (F '' K) := by
    intro z hz
    constructor
    · rintro ⟨w, hw, heq⟩
      exact F.injOn (hK hw) hz heq ▸ hw
    · exact mem_image_of_mem F
  simpa only [inter_eq_right.mpr (interior_subset.trans hK),
    inter_eq_right.mpr (interior_subset.trans himage)] using
    himage_eq.interior.image_eq.symm

omit [T2Space M] in

theorem coordinate_triangle_interior_nonempty
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : convexHull ℝ (range b) ⊆ F.source) :
    (interior (F '' convexHull ℝ (range b))).Nonempty := by
  rw [interior_smooth_coordinate_image F hsub]
  exact Set.Nonempty.image F ⟨_, b.centroid_mem_interior_convexHull⟩

theorem coordinate_triangle_closure_interior
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : convexHull ℝ (range b) ⊆ F.source) :
    closure (interior (F '' convexHull ℝ (range b))) = F '' convexHull ℝ (range b) := by
  have hcompact := (finite_range b).isCompact_convexHull ℝ
  have hclosed := (hcompact.image_of_continuousOn (F.continuousOn.mono hsub)).isClosed
  have hregular : closure (interior (convexHull ℝ (range b))) = convexHull ℝ (range b) := by
    rw [(convex_convexHull ℝ (range b)).closure_interior_eq_closure_of_nonempty_interior
      ⟨_, b.centroid_mem_interior_convexHull⟩, hcompact.isClosed.closure_eq]
  apply subset_antisymm (closure_minimal interior_subset hclosed)
  rw [interior_smooth_coordinate_image F hsub]
  have hdomain : closure (interior (convexHull ℝ (range b))) ⊆ F.source := by
    rwa [hregular]
  have himage : F '' closure (interior (convexHull ℝ (range b))) ⊆
      closure (F '' interior (convexHull ℝ (range b))) :=
    (F.continuousOn.mono hdomain).image_closure
  rwa [hregular] at himage

end PoincareConjecture.Topology.Surface
