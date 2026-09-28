import PoincareConjecture.Proofs.M38.SphereAffineChart
import PoincareConjecture.Proofs.M38.ProjectiveModel
import PoincareConjecture.Proofs.M38.CompactCoverSheet
import PoincareConjecture.Proofs.M38.SurgeryBallNeighborhood
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

open Poincare.Topology

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

attribute [local instance] projectiveLiftChartedSpace projective_lift_isManifold

noncomputable def sphereOrthogonalDiffeomorph
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Diffeomorph (𝓡 3) (𝓡 3) UnitThreeSphere UnitThreeSphere ∞ where
  toFun x := ⟨R x.val, by simpa only [Metric.mem_sphere, dist_zero_right,
    LinearIsometryEquiv.norm_map] using x.property⟩
  invFun x := ⟨R.symm x.val, by simpa only [Metric.mem_sphere, dist_zero_right,
    LinearIsometryEquiv.norm_map] using x.property⟩
  left_inv x := Subtype.ext (R.symm_apply_apply x.val)
  right_inv x := Subtype.ext (R.apply_symm_apply x.val)
  contMDiff_toFun :=
    (R.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _
  contMDiff_invFun :=
    (R.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _

theorem sphereOrthogonalDiffeomorph_neg
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (x : UnitThreeSphere) :
    sphereOrthogonalDiffeomorph R (-x) = -sphereOrthogonalDiffeomorph R x :=
  Subtype.ext (map_neg R x.val)

noncomputable def projectiveAffineMap
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (x : StandardCapSpace) : projectiveCarrier.{u}.carrier :=
  liftedProjectiveCover.cover (sphereOrthogonalDiffeomorph R (sphereAffineMap x))

theorem projectiveAffineMap_injective
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Function.Injective (projectiveAffineMap.{u} R) := by
  intro x y h
  rcases (liftedProjectiveCover.fibers _ _).mp h with h | h
  · exact Function.LeftInverse.injective sphereAffine_left_inverse
      ((sphereOrthogonalDiffeomorph R).injective h)
  · rw [← sphereOrthogonalDiffeomorph_neg] at h
    have hxy := (sphereOrthogonalDiffeomorph R).injective h
    have hzero := congrArg (fun z : UnitThreeSphere => z.val 0) hxy
    have hx := sphereAffineMap_positive x
    have hy := sphereAffineMap_positive y
    change (sphereAffineMap x).val 0 = -(sphereAffineMap y).val 0 at hzero
    linarith

theorem projectiveAffineMap_localDiffeomorph
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (projectiveAffineMap.{u} R) := by
  intro x
  exact ((sphereAffineChart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
    (mem_univ x)).comp (𝓡 3) UnitThreeSphere
    ((sphereOrthogonalDiffeomorph R).isLocalDiffeomorph _)).comp
      (𝓡 3) projectiveCarrier.carrier (liftedProjectiveCover.local_diffeomorph _)

theorem exists_projectiveAffineChart
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    ∃ e : PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace
        projectiveCarrier.{u}.carrier ∞,
      e.source = univ ∧ e.target = range (projectiveAffineMap R) ∧
        (e : StandardCapSpace → projectiveCarrier.carrier) = projectiveAffineMap R := by
  simpa only [image_univ] using localDiffeomorph_injective_open_sheet_generic
    (projectiveAffineMap.{u} R) (projectiveAffineMap_localDiffeomorph R)
    isOpen_univ (projectiveAffineMap_injective R).injOn

theorem sphereAffineMap_zero : sphereAffineMap 0 = spherePolarPole 2 := by
  have hv : sphereAffineVector 0 = (spherePolarPole 2).val := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [sphereAffineVector, spherePolarPole]
  apply Subtype.ext
  change ‖sphereAffineVector 0‖⁻¹ • sphereAffineVector 0 = _
  rw [hv, norm_eq_of_mem_sphere, inv_one, one_smul]

theorem exists_projectiveAffineReferenceBall (p : projectiveCarrier.{u}.carrier) :
    ∃ R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4),
    ∃ B : SurgeryBallEmbedding projectiveCarrier.{u},
      B.map = projectiveAffineMap R ∧ B.map 0 = p := by
  let a := projectiveRepresentative p.down
  let R := (ℝ ∙ ((spherePolarPole 2).val - a.val))ᗮ.reflection
  have hR : R (spherePolarPole 2).val = a.val :=
    Submodule.reflection_sub (by simp)
  obtain ⟨e, hes, _, he⟩ := exists_projectiveAffineChart.{u} R
  let B : SurgeryBallEmbedding projectiveCarrier.{u} := {
    map := e
    inverse := e.symm
    map_smooth := e.contMDiffOn_toFun.mono (hes.symm ▸ subset_univ _)
    inverse_smooth := e.contMDiffOn_invFun.mono (by
      rintro y ⟨x, hx, rfl⟩
      exact e.map_source (hes.symm ▸ mem_univ x))
    left_inverse := fun x _ => e.toPartialEquiv.left_inv (hes.symm ▸ mem_univ x)
    right_inverse := by
      rintro y ⟨x, hx, rfl⟩
      exact e.toPartialEquiv.right_inv (e.map_source (hes.symm ▸ mem_univ x))
    open_embedding := (e.toOpenPartialHomeomorph.isOpenEmbedding hes).comp
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal }
  refine ⟨R, B, he, ?_⟩
  change e 0 = p
  rw [he]
  change liftedProjectiveCover.cover (sphereOrthogonalDiffeomorph R (sphereAffineMap 0)) = p
  rw [sphereAffineMap_zero]
  have ha : sphereOrthogonalDiffeomorph R (spherePolarPole 2) = a := Subtype.ext hR
  rw [ha]
  exact congrArg ULift.up (projectiveRepresentative_spec p.down)

end PoincareConjecture.M38
