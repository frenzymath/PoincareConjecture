import PoincareConjecture.Proofs.M11.OrdinaryCharts





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

noncomputable def spatialChartHomeomorph (p : M) :
    OpenPartialHomeomorph (spatialChartDomain (n := n) p) M := by
  letI : Nonempty (spatialChartDomain (n := n) p) :=
    ⟨⟨chartAt (EuclideanSpace ℝ (Fin n)) p p, mem_chart_target _ p⟩⟩
  exact (spatialChartInverse_openEmbedding p).toOpenPartialHomeomorph (spatialChartInverse p)

theorem spatialChartHomeomorph_target (p : M) :
    (spatialChartHomeomorph (n := n) p).target =
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  rw [spatialChartHomeomorph, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact c.map_target y.property
  · intro hx
    exact ⟨⟨c x, c.map_source hx⟩, c.left_inv hx⟩

theorem spatialChartHomeomorph_inverse_eq (p x : M)
    (hx : x ∈ (spatialChartHomeomorph (n := n) p).target) :
    ((spatialChartHomeomorph p).symm x).val = chartAt (EuclideanSpace ℝ (Fin n)) p x := by
  let e := spatialChartHomeomorph (n := n) p
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  have h := congrArg c (e.right_inv hx)
  change c (c.symm (e.symm x).val) = c x at h
  rw [c.right_inv (e.symm x).property] at h
  exact h

theorem spatialChartHomeomorph_inverse_smooth [IsManifold (𝓡 n) ∞ M] (p : M) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (spatialChartHomeomorph (n := n) p).symm
      (spatialChartHomeomorph (n := n) p).target := by
  intro x hx
  apply (ContMDiffWithinAt.subtypeVal_comp_iff (spatialChartDomain p) _ _ x).mp
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt (EuclideanSpace ℝ (Fin n)) p)
      (spatialChartHomeomorph (n := n) p).target := by
    rw [spatialChartHomeomorph_target]
    exact contMDiffOn_chart
  apply (hc x hx).congr_of_mem _ hx
  intro y hy
  exact spatialChartHomeomorph_inverse_eq (n := n) p y hy

end PoincareConjecture.Proofs.M11
