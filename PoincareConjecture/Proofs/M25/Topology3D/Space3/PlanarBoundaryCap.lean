import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscCap











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] space3_stereographic_dimension



theorem boundaryDisc_cap_of_planar (hP : PlanarSchoenfliesService)
    (c : UnitCircle → E2) (hc : IsPlanarEmbedding c) (v : UnitTwoSphere) :
    ∃ D : PlanarSchoenfliesData c, ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        (∀ y, ‖F y‖ = ‖y‖) ∧
        F '' ((fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) ''
          closedBall 0 1) = {y : E3 | ‖y‖ = 1 ∧ a ≤ ⟪-(v : E3), y⟫_ℝ} ∧
        ∃ C : Set E3, IsCompact C ∧ ∀ y, y ∉ C → F y = y := by
  obtain ⟨D⟩ := hP.1 c hc
  let U : (ℝ ∙ (v : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
  let B := D.ballNeighborhoodChart.isometryConjugate U
  have hdim : 1 < Module.rank ℝ ((ℝ ∙ (v : E3))ᗮ) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [U.toLinearEquiv.finrank_eq]
    simp [E2]
  have hdim3 : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  have hsphere : IsPreconnected (sphere (0 : E3) 1) :=
    (isConnected_sphere hdim3 0 zero_le_one).isPreconnected
  obtain ⟨a, ha, F, hFnorm, himage, C, hC, hfix⟩ :=
    exists_boundary_disc_cap (v : E3) (norm_eq_of_mem_sphere v) B hdim hsphere
  refine ⟨D, a, ha, F, hFnorm, ?_, C, hC, hfix⟩
  have hcoordinates : (fun w => (stereoInvFun (norm_eq_of_mem_sphere v) w : E3)) ''
      B.closedRegion =
      (fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) '' closedBall 0 1 := by
    ext y
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨U w, ?_, rfl⟩
      simpa only [mem_closedBall_zero_iff, U.norm_map] using hw
    · rintro ⟨x, hx, rfl⟩
      have hxU : U.symm x ∈ closedBall (0 : (ℝ ∙ (v : E3))ᗮ) 1 := by
        simpa only [mem_closedBall_zero_iff, U.symm.norm_map] using hx
      refine ⟨B.chart (U.symm x), ⟨U.symm x, hxU, rfl⟩, ?_⟩
      change (stereoInvFun (norm_eq_of_mem_sphere v)
          (U.symm (D.chart (U (U.symm x)))) : E3) =
        (stereoInvFun (norm_eq_of_mem_sphere v) (U.symm (D.chart x)) : E3)
      rw [U.apply_symm_apply]
  rw [← hcoordinates]
  exact himage

end PoincareConjecture.M25.Topology3D
