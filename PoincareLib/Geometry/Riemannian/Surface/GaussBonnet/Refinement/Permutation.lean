import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.MetricCorners

/-!
# Metric corner angles under vertex permutations

Reindexing an affine triangle preserves each actual outgoing side velocity.
The two rays at a corner can only exchange order, so the metric corner angle
and the sum of all three corner angles are invariant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.Topology.Surface

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [IsManifold (𝓡 2) ∞ S] in
/-- Reindexing changes only the labels of the actual side velocities. -/
theorem coordinateTriangleVelocity_reindex
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (e : Fin 3 ≃ Fin 3) (i j : Fin 3) :
    coordinateTriangleVelocity F (b.reindex e) i j =
      coordinateTriangleVelocity F b (e.symm i) (e.symm j) := rfl

private theorem reindex_complementary_vertices (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    (e.symm (i.succAbove 0) = (e.symm i).succAbove 0 ∧
      e.symm (i.succAbove 1) = (e.symm i).succAbove 1) ∨
    (e.symm (i.succAbove 0) = (e.symm i).succAbove 1 ∧
      e.symm (i.succAbove 1) = (e.symm i).succAbove 0) := by
  have h0 : e.symm (i.succAbove 0) ≠ e.symm i :=
    fun h => Fin.succAbove_ne i 0 (e.symm.injective h)
  have h1 : e.symm (i.succAbove 1) ≠ e.symm i :=
    fun h => Fin.succAbove_ne i 1 (e.symm.injective h)
  obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq h0
  obtain ⟨v, hv⟩ := Fin.exists_succAbove_eq h1
  have huv : u ≠ v := by
    intro huv
    have h := hu.symm.trans (huv ▸ hv)
    exact (by decide : (0 : Fin 2) ≠ 1)
      (Fin.succAbove_right_injective (e.symm.injective h))
  fin_cases u <;> fin_cases v <;> simp_all

/-- The actual metric corner at a reindexed vertex has the original angle. -/
theorem coordinateTriangleAngle_reindex (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    coordinateTriangleAngle g F (b.reindex e) i =
      coordinateTriangleAngle g F b (e.symm i) := by
  simp only [coordinateTriangleAngle, coordinateTriangleVelocity_reindex, AffineBasis.reindex_apply]
  rcases reindex_complementary_vertices e i with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1]
  · rw [h0, h1]
    exact g.cornerAngle_comm _ _ _

/-- A permutation of a face's ordered vertices preserves its total metric
corner contribution. -/
theorem sum_coordinateTriangleAngle_reindex (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (e : Fin 3 ≃ Fin 3) :
    (∑ i : Fin 3, coordinateTriangleAngle g F (b.reindex e) i) =
      ∑ i : Fin 3, coordinateTriangleAngle g F b i := by
  simp only [coordinateTriangleAngle_reindex]
  exact e.symm.sum_comp (coordinateTriangleAngle g F b)

end PoincareMT.Topology.Surface
