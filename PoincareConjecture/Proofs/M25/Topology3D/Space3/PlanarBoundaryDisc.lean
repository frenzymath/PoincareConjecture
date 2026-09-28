import PoincareConjecture.Proofs.M25.Topology3D.Space3.StandardTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallChartIsometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscShrinking

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local instance space3_stereographic_dimension : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨by simp [E3]⟩

noncomputable def PlanarSchoenfliesData.ballNeighborhoodChart {c : UnitCircle → E2}
    (D : PlanarSchoenfliesData c) : BallNeighborhoodChart E2 E2 where
  chart := D.discChart
  closedBall_subset_source := D.closedBall_subset_discChart_source
  smooth := D.discChart_contDiffOn
  smooth_symm := D.discChart_symm_contDiffOn

theorem boundaryDisc_shrinking_of_planar (hP : PlanarSchoenfliesService)
    (c : UnitCircle → E2) (hc : IsPlanarEmbedding c) (v : UnitTwoSphere) :
    ∃ D : PlanarSchoenfliesData c,
      ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        ContDiff ℝ ∞ (fun p : ℝ × E3 => Φ p.1 p.2) ∧
        (∀ y, Φ 0 y = y) ∧
        (∀ t y, ‖Φ t y‖ = ‖y‖) ∧
        (∀ x ∈ closedBall (0 : E2) 1, ∀ t : ℝ, 0 ≤ t →
          Φ t ((stereographic' 2 v).symm (D.chart x) : E3) =
            ((stereographic' 2 v).symm (D.chart (Real.exp (-t) • x)) : E3)) ∧
        ∃ C : Set E3, IsCompact C ∧ ∀ t y, y ∉ C → Φ t y = y := by
  obtain ⟨D⟩ := hP.1 c hc
  let U : (ℝ ∙ (v : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
  let B := D.ballNeighborhoodChart.isometryConjugate U
  obtain ⟨Φ, hΦ, hzero, hnorm, htrack, _, C, hC, _, hfix⟩ :=
    exists_boundaryDisc_shrinking_isotopy (v : E3) (norm_eq_of_mem_sphere v) B
  refine ⟨D, Φ, hΦ, hzero, hnorm, ?_, C, hC, hfix⟩
  intro x hx t ht
  have hxU : U.symm x ∈ closedBall (0 : (ℝ ∙ (v : E3))ᗮ) 1 := by
    simpa only [mem_closedBall_zero_iff, U.symm.norm_map] using hx
  have h := htrack (U.symm x) hxU t ht
  change Φ t (stereoInvFun (norm_eq_of_mem_sphere v)
      (U.symm (D.chart (U (U.symm x)))) : E3) =
    (stereoInvFun (norm_eq_of_mem_sphere v)
      (U.symm (D.chart (U (Real.exp (-t) • U.symm x)))) : E3) at h
  rw [U.apply_symm_apply, map_smul, U.apply_symm_apply] at h
  exact h

end PoincareConjecture.M25.Topology3D
