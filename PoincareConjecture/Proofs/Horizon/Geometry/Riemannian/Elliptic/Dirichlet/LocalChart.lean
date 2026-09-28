import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_precompact_coordinate_neighborhood
    {Ω : Set M} (hΩ : IsOpen Ω) {x : M} (hx : x ∈ Ω) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧ K ⊆ e.source ∧
        ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ O ⊆ K ∧
          x ∈ e '' O ∧ e '' O ⊆ Ω ∧ K ⊆ e ⁻¹' Ω := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
  have hxT : x ∈ e.target := mem_chart_source _ _
  have hxS : e.symm x ∈ e.source ∩ e ⁻¹' Ω :=
    ⟨e.map_target hxT, by simpa only [mem_preimage, e.right_inv hxT] using hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((e.isOpen_inter_preimage hΩ).mem_nhds hxS)
  refine ⟨e, contMDiffOn_chart_symm, contMDiffOn_chart,
    Metric.closedBall (e.symm x) r, isCompact_closedBall _ _,
    hball.trans inter_subset_left, Metric.ball (e.symm x) r, Metric.isOpen_ball,
    Metric.ball_subset_closedBall, ?_, ?_, hball.trans inter_subset_right⟩
  · exact ⟨e.symm x, Metric.mem_ball_self hr, e.right_inv hxT⟩
  · rintro y ⟨z, hz, rfl⟩
    exact (hball (Metric.ball_subset_closedBall hz)).2

end PoincareConjecture
