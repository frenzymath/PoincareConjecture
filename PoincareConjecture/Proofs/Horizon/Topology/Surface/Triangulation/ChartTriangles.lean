


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.ChartCover
import Mathlib.Analysis.Normed.Affine.Convex













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]



theorem exists_chart_triangle (x : M) :
    ∃ b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)),
      chartAt (EuclideanSpace ℝ (Fin 2)) x x ∈ interior (convexHull ℝ (range b)) ∧
      convexHull ℝ (range b) ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) x).target := by
  have h := exists_mem_interior_convexHull_affineBasis
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).map_source (mem_chart_source _ x)))
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 :=
    finrank_euclideanSpace_fin
  rw [hdim] at h
  exact h



theorem exists_finite_chart_triangle_cover [CompactSpace M] :
    ∃ (s : Finset M) (b : M → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2))),
      (∀ x, chartAt (EuclideanSpace ℝ (Fin 2)) x x ∈
        interior (convexHull ℝ (range (b x)))) ∧
      (∀ x, convexHull ℝ (range (b x)) ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) ∧
      (⋃ x ∈ s, interior ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        convexHull ℝ (range (b x)))) = (univ : Set M) := by
  classical
  choose b hcenter hsub using exists_chart_triangle (M := M)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => interior ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      convexHull ℝ (range (b x)))) (fun _ => isOpen_interior) (by
        intro x _
        apply mem_iUnion.mpr
        refine ⟨x, ?_⟩
        rw [interior_chart_image x (hsub x)]
        exact ⟨_, hcenter x,
          (chartAt (EuclideanSpace ℝ (Fin 2)) x).left_inv (mem_chart_source _ x)⟩)
  exact ⟨s, b, hcenter, hsub, Subset.antisymm (subset_univ _) hs⟩

end PoincareConjecture.Topology.Surface
