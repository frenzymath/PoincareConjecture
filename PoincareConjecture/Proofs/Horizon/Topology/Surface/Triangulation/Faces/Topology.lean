import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface.SmoothFace

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem isCompact_carrier_image (f : SmoothFace M) : IsCompact f.carrier := by
  rw [f.carrier_eq_image]
  exact f.source_compact.image_of_continuousOn f.smooth.continuousOn

theorem isClosed_carrier [T2Space M] (f : SmoothFace M) : IsClosed f.carrier :=
  f.isCompact_carrier_image.isClosed

theorem boundary_image_subset_frontier (f : SmoothFace M) (k : Fin 3) :
    (f.boundary k).map '' Icc (0 : ℝ) 1 ⊆ frontier f.carrier := by
  rw [f.boundary_carrier]
  exact subset_iUnion (fun i => (f.boundary i).map '' Icc (0 : ℝ) 1) k

theorem interior_boundary_image [T2Space M] (f : SmoothFace M) (k : Fin 3) :
    interior ((f.boundary k).map '' Icc (0 : ℝ) 1) = ∅ := by
  apply subset_empty_iff.mp
  rw [← interior_frontier f.isClosed_carrier]
  exact interior_mono (f.boundary_image_subset_frontier k)

theorem disjoint_interiors_of_inter_subset_frontier (f g : SmoothFace M)
    (h : f.carrier ∩ g.carrier ⊆ frontier f.carrier) :
    Disjoint (interior f.carrier) (interior g.carrier) := by
  exact disjoint_left.mpr fun _ hf hg =>
    disjoint_left.mp disjoint_interior_frontier hf (h ⟨interior_subset hf, interior_subset hg⟩)

end PoincareConjecture.Topology.Surface.SmoothFace
