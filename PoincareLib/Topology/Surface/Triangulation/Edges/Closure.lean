/-
Copyright (c) 2026 The PoincareLib contributors.
-/
import PoincareLib.Topology.Surface.Triangulation.Basic

/-!
# Closure of the interior of a smooth edge

Closed-set containment of an edge is determined by its open parameter interval.
This transfers uniform interior incidence to the whole closed edge image.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- A closed set contains a smooth edge exactly when it contains the image
of the open parameter interval. -/
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

end PoincareMT.Topology.Surface
