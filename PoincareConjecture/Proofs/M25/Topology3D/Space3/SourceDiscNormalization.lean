import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscRounding
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereDiffeomorphRestriction

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] space3_stereographic_dimension

theorem sourceDisc_round_of_planarData {c : UnitCircle → E2}
    (D : PlanarSchoenfliesData c) (v : UnitTwoSphere) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∃ G : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
        G '' ((D.discChart.trans (stereographic' 2 v).symm) '' closedBall 0 1) =
          (stereographic' 2 v).symm '' closedBall 0 r := by
  let U : (ℝ ∙ (v : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
  let B := D.ballNeighborhoodChart.isometryConjugate U
  have hdim : 1 < Module.rank ℝ ((ℝ ∙ (v : E3))ᗮ) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [U.toLinearEquiv.finrank_eq]
    simp [E2]
  have hdim3 : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  obtain ⟨r, hr, hr1, F, hF, himage, _⟩ := exists_boundary_disc_round_image
    (v : E3) (norm_eq_of_mem_sphere v) B hdim
      (isConnected_sphere hdim3 0 zero_le_one).isPreconnected
  let G := normPreservingSphereDiffeomorph (n := 2) F hF
  refine ⟨r, hr, hr1, G, ?_⟩
  apply (Subtype.coe_injective : Function.Injective
    ((↑) : UnitTwoSphere → E3)).image_injective
  have hdisc : (fun w => (stereoInvFun (norm_eq_of_mem_sphere v) w : E3)) ''
      B.closedRegion =
      ((↑) : UnitTwoSphere → E3) ''
        ((D.discChart.trans (stereographic' 2 v).symm) '' closedBall 0 1) := by
    rw [image_image]
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
  have hround : (fun w => (stereoInvFun (norm_eq_of_mem_sphere v) w : E3)) ''
      closedBall 0 r =
      ((↑) : UnitTwoSphere → E3) '' ((stereographic' 2 v).symm '' closedBall 0 r) := by
    calc
      _ = (fun w => (stereoInvFun (norm_eq_of_mem_sphere v) w : E3)) ''
          (U.symm '' closedBall 0 r) := by rw [U.symm.image_closedBall, map_zero]
      _ = _ := by rw [image_image, image_image]; rfl
  rw [hdisc, hround] at himage
  simpa only [image_image, G, normPreservingSphereDiffeomorph_apply] using himage

end PoincareConjecture.M25.Topology3D
