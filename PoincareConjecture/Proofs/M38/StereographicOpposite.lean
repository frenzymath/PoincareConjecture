import PoincareConjecture.Proofs.M38.ThreeSphereConnection
import PoincareConjecture.Definitions.Ch12.StandardCap










set_option autoImplicit false

open Set
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩


noncomputable def threeSphereStereoFrame (a : UnitThreeSphere) :
    (ℝ ∙ (a : EuclideanSpace ℝ (Fin 4)))ᗮ ≃ₗᵢ[ℝ] StandardCapSpace :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere a)).repr


theorem threeSphereStereo_opposite_plane (a : UnitThreeSphere) :
    (ℝ ∙ ((-a : UnitThreeSphere) : EuclideanSpace ℝ (Fin 4)))ᗮ =
      (ℝ ∙ (a : EuclideanSpace ℝ (Fin 4)))ᗮ := by
  congr 1
  change Submodule.span ℝ {-(a : EuclideanSpace ℝ (Fin 4))} =
    Submodule.span ℝ {(a : EuclideanSpace ℝ (Fin 4))}
  rw [← Set.neg_singleton]
  exact Submodule.span_neg _


noncomputable def threeSphereStereoOppositeIsometry (a : UnitThreeSphere) :
    StandardCapSpace ≃ₗᵢ[ℝ] StandardCapSpace :=
  ((threeSphereStereoFrame (-a)).symm.trans
    (LinearIsometryEquiv.ofEq _ _ (threeSphereStereo_opposite_plane a))).trans
      (threeSphereStereoFrame a)


theorem threeSphereStereoOppositeIsometry_vector (a : UnitThreeSphere)
    (x : StandardCapSpace) :
    (((threeSphereStereoFrame a).symm (threeSphereStereoOppositeIsometry a x)) :
      EuclideanSpace ℝ (Fin 4)) =
        (((threeSphereStereoFrame (-a)).symm x) : EuclideanSpace ℝ (Fin 4)) := by
  simp only [threeSphereStereoOppositeIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rfl





theorem threeSphereStereo_opposite (a : UnitThreeSphere)
    (x : StandardCapSpace) (hx : x ≠ 0) :
    stereographic' 3 a ((stereographic' 3 (-a)).symm x) =
      (4 / ‖x‖ ^ 2) • threeSphereStereoOppositeIsometry a x := by
  let U := threeSphereStereoFrame a
  let V := threeSphereStereoFrame (-a)
  let w := V.symm x
  let w' := LinearIsometryEquiv.ofEq _ _ (threeSphereStereo_opposite_plane a) w
  have hw : (w' : EuclideanSpace ℝ (Fin 4)) = w := rfl
  have hnorm : ‖(w : EuclideanSpace ℝ (Fin 4))‖ = ‖x‖ := by
    change ‖V.symm x‖ = ‖x‖
    exact V.symm.norm_map x
  have hiw : ⟪(a : EuclideanSpace ℝ (Fin 4)), (w : EuclideanSpace ℝ (Fin 4))⟫_ℝ = 0 := by
    rw [← hw]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w'.property
  have hia : ⟪(a : EuclideanSpace ℝ (Fin 4)),
      ((-a : UnitThreeSphere) : EuclideanSpace ℝ (Fin 4))⟫_ℝ = -1 := by
    simp [real_inner_self_eq_norm_sq]
  have hpw : (ℝ ∙ (a : EuclideanSpace ℝ (Fin 4)))ᗮ.orthogonalProjectionOnto
      (w : EuclideanSpace ℝ (Fin 4)) = w' := by
    rw [← hw]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self w'
  have hpa : (ℝ ∙ (a : EuclideanSpace ℝ (Fin 4)))ᗮ.orthogonalProjectionOnto
      (((-a : UnitThreeSphere) : EuclideanSpace ℝ (Fin 4))) = 0 := by
    change (ℝ ∙ (a : EuclideanSpace ℝ (Fin 4)))ᗮ.orthogonalProjectionOnto
      (-(a : EuclideanSpace ℝ (Fin 4))) = 0
    rw [map_neg, Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
      neg_zero]
  have hcoord : (((stereographic' 3 (-a)).symm x) : EuclideanSpace ℝ (Fin 4)) =
      (‖x‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (w : EuclideanSpace ℝ (Fin 4)) +
        (‖x‖ ^ 2 + 4)⁻¹ • (‖x‖ ^ 2 - 4) •
          (((-a : UnitThreeSphere) : EuclideanSpace ℝ (Fin 4))) := by
    rw [stereographic'_symm_apply]
    change (‖(w : EuclideanSpace ℝ (Fin 4))‖ ^ 2 + 4)⁻¹ • (4 : ℝ) •
        (w : EuclideanSpace ℝ (Fin 4)) +
      (‖(w : EuclideanSpace ℝ (Fin 4))‖ ^ 2 + 4)⁻¹ •
        (‖(w : EuclideanSpace ℝ (Fin 4))‖ ^ 2 - 4) •
          (((-a : UnitThreeSphere) : EuclideanSpace ℝ (Fin 4))) = _
    rw [hnorm]
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hp : ‖x‖ ^ 2 + 4 ≠ 0 := ne_of_gt (by positivity)
  have hden : 1 - (‖x‖ ^ 2 + 4)⁻¹ * ((‖x‖ ^ 2 - 4) * (-1)) =
      (2 * ‖x‖ ^ 2) / (‖x‖ ^ 2 + 4) := by
    field_simp
    <;> ring
  have hscalar : (2 / (1 - (‖x‖ ^ 2 + 4)⁻¹ * ((‖x‖ ^ 2 - 4) * (-1)))) *
      ((‖x‖ ^ 2 + 4)⁻¹ * 4) = 4 / ‖x‖ ^ 2 := by
    rw [hden]
    field_simp
  change U ((2 / (1 - ⟪(a : EuclideanSpace ℝ (Fin 4)),
      (((stereographic' 3 (-a)).symm x) : EuclideanSpace ℝ (Fin 4))⟫_ℝ)) •
        (ℝ ∙ (a : EuclideanSpace ℝ (Fin 4)))ᗮ.orthogonalProjectionOnto
          (((stereographic' 3 (-a)).symm x) : EuclideanSpace ℝ (Fin 4))) = _
  rw [hcoord]
  simp only [inner_add_right, real_inner_smul_right, hiw, hia, mul_zero, zero_add,
    map_add, map_smul, hpw, hpa, smul_zero, add_zero, smul_smul]
  change (2 / (1 - (‖x‖ ^ 2 + 4)⁻¹ * (‖x‖ ^ 2 - 4) * (-1)) *
      ((‖x‖ ^ 2 + 4)⁻¹ * 4)) • U w' = (4 / ‖x‖ ^ 2) • U w'
  exact congrArg (fun r : ℝ => r • U w') (by simpa only [mul_assoc] using hscalar)



theorem threeSphereStereo_opposite_ray (a : UnitThreeSphere)
    (z : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    stereographic' 3 a ((stereographic' 3 (-a)).symm (r • z.val)) =
      (4 / r) • threeSphereStereoOppositeIsometry a z.val := by
  have hz : z.val ≠ 0 := ne_zero_of_mem_unit_sphere z
  rw [threeSphereStereo_opposite a _ (smul_ne_zero hr.ne' hz),
    norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    show ‖z.val‖ = 1 by simp, mul_one, map_smul, smul_smul]
  congr 1
  field_simp

end PoincareConjecture.M38
