import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem SmoothEdge.image_Icc_subset_closed_iff (e : SmoothEdge M)
    {A : Set M} (hA : IsClosed A) :
    e.map '' Icc (0 : ℝ) 1 ⊆ A ↔ e.map '' Ioo (0 : ℝ) 1 ⊆ A := by
  refine ⟨fun h => (image_mono Ioo_subset_Icc_self).trans h, ?_⟩
  intro h
  have hm : MapsTo e.map (Ioo (0 : ℝ) 1) A := fun t ht => h ⟨t, ht, rfl⟩
  have hc := hm.closure_of_continuousOn (show ContinuousOn e.map (closure (Ioo (0 : ℝ) 1)) by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact e.smooth.continuousOn)
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), hA.closure_eq] at hc
  exact hc.image_subset

end PoincareConjecture.Topology.Surface
