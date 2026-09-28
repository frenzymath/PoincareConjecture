import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.LinearBall



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

private theorem linearBall_mem_sphere (A : E2 ≃L[Real] E2) (p : S1) :
    LinearBall.neighborhood A p ∈ sphere (0 : E2) 1 := by
  have hA : A (p : E2) ≠ 0 := fun h =>
    ne_zero_of_mem_unit_sphere p (A.injective (h.trans A.map_zero.symm))
  rw [LinearBall.apply_of_mem_sphere A p.property, mem_sphere_zero_iff_norm, norm_smul]
  simp [norm_ne_zero_iff.mpr hA]


def linearAction (A : E2 ≃L[Real] E2) : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞ where
  toFun p := ⟨LinearBall.neighborhood A p, linearBall_mem_sphere A p⟩
  invFun p := ⟨LinearBall.neighborhood A.symm p, linearBall_mem_sphere A.symm p⟩
  left_inv p := Subtype.ext
    ((LinearBall.neighborhood A).left_inv
      (LinearBall.closedBall_subset_source A (sphere_subset_closedBall p.property)))
  right_inv p := Subtype.ext
    ((LinearBall.neighborhood A).right_inv
      (LinearBall.closedBall_subset_target A (sphere_subset_closedBall p.property)))
  contMDiff_toFun := by
    apply ContMDiff.codRestrict_sphere
    intro p
    exact ((LinearBall.contMDiffOn_neighborhood A).contMDiffAt
      ((LinearBall.neighborhood A).open_source.mem_nhds
        (LinearBall.closedBall_subset_source A (sphere_subset_closedBall p.property)))).comp p
      (contMDiff_coe_sphere p)
  contMDiff_invFun := by
    apply ContMDiff.codRestrict_sphere
    intro p
    exact ((LinearBall.contMDiffOn_neighborhood A.symm).contMDiffAt
      ((LinearBall.neighborhood A.symm).open_source.mem_nhds
        (LinearBall.closedBall_subset_source A.symm
          (sphere_subset_closedBall p.property)))).comp p (contMDiff_coe_sphere p)

theorem linearAction_apply (A : E2 ≃L[Real] E2) (p : S1) :
    (linearAction A p : E2) = ‖A (p : E2)‖⁻¹ • A (p : E2) :=
  LinearBall.apply_of_mem_sphere A p.property

theorem linearAction_isometry_apply (A : E2 ≃ₗᵢ[Real] E2) (p : S1) :
    (linearAction A.toContinuousLinearEquiv p : E2) = A (p : E2) := by
  rw [linearAction_apply]
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    A.norm_map, norm_eq_of_mem_sphere, inv_one, one_smul]


theorem linearAction_hemisphere (p : S1)
    (L : Hemisphere.Plane (p : E2) ≃L[Real] Hemisphere.Plane (p : E2))
    (x : Hemisphere.Plane (p : E2)) :
    linearAction (Hemisphere.extendLinear p L)
        (Hemisphere.chart (norm_eq_of_mem_sphere p) x) =
      Hemisphere.chart (norm_eq_of_mem_sphere p) (L x) := by
  apply Subtype.ext
  rw [linearAction_apply]
  exact Hemisphere.normalized_linear_chart (norm_eq_of_mem_sphere p) _ L
    (Hemisphere.extendLinear_center L) (Hemisphere.extendLinear_plane L) x

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
