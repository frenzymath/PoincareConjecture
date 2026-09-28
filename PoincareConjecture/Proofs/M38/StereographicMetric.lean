import PoincareConjecture.Proofs.M38.ThreeSphereConnection










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩



noncomputable def stereoDifferential
    (a : EuclideanSpace ℝ (Fin 4))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (z : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (4 / (‖z‖ ^ 2 + 4)) • L.toContinuousLinearMap -
    (8 / (‖z‖ ^ 2 + 4) ^ 2) • (innerSL ℝ z).smulRight (L z) +
    (16 / (‖z‖ ^ 2 + 4) ^ 2) • (innerSL ℝ z).smulRight a



theorem hasFDerivAt_stereo_comp_isometry
    (a : EuclideanSpace ℝ (Fin 4))
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (z : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (fun y => stereoInvFunAux a (L y)) (stereoDifferential a L z) z := by
  have hd : ‖z‖ ^ 2 + 4 ≠ (0 : ℝ) := by positivity
  have hq := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hi := (hasFDerivAt_inv hd).comp z (hq.add_const 4)
  have hv := (L.toContinuousLinearMap.hasFDerivAt.const_smul (4 : ℝ)).add
    ((hq.sub_const 4).smul_const a)
  convert! hi.smul hv using 1
  · funext y
    change stereoInvFunAux a (L y) =
      (‖y‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • L y + (‖y‖ ^ 2 - 4) • a)
    rw [stereoInvFunAux_apply, L.norm_map]
  · ext u i
    simp only [stereoDifferential, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      Function.comp_apply, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_smul,
      LinearIsometry.coe_toContinuousLinearMap, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, smul_add, add_smul, mul_smul]
    field_simp
    <;> ring



theorem stereoDifferential_inner
    (a : UnitThreeSphere)
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (hL : ∀ z, inner ℝ (a : EuclideanSpace ℝ (Fin 4)) (L z) = 0)
    (z u v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (stereoDifferential a L z u) (stereoDifferential a L z v) =
      (16 / (‖z‖ ^ 2 + 4) ^ 2) * inner ℝ u v := by
  have hd : ‖z‖ ^ 2 + 4 ≠ (0 : ℝ) := by positivity
  have hLa (w) : inner ℝ (L w) (a : EuclideanSpace ℝ (Fin 4)) = 0 := by
    rw [real_inner_comm, hL]
  have haa : inner ℝ (a : EuclideanSpace ℝ (Fin 4)) a = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere a]
    norm_num
  simp only [stereoDifferential, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    LinearIsometry.coe_toContinuousLinearMap, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    L.inner_map_map, hL, hLa, haa, real_inner_self_eq_norm_sq]
  rw [real_inner_comm z u]
  field_simp
  <;> ring



noncomputable def sphereStereoPlane (a : UnitThreeSphere) :
    EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ((ℝ ∙ (a : EuclideanSpace ℝ (Fin 4)))ᗮ.subtypeₗᵢ).comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere a)).repr.symm.toLinearIsometry


theorem sphereStereoPlane_orthogonal (a : UnitThreeSphere)
    (z : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (a : EuclideanSpace ℝ (Fin 4)) (sphereStereoPlane a z) = 0 := by
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere a)).repr.symm z).property



theorem threeSphereStereoInverse_coe (a : UnitThreeSphere)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (threeSphereStereoInverse a z : EuclideanSpace ℝ (Fin 4)) =
      stereoInvFunAux (a : EuclideanSpace ℝ (Fin 4)) (sphereStereoPlane a z) := by
  rw [threeSphereStereoInverse, stereographic'_symm_apply]
  change _ = stereoInvFunAux (a : EuclideanSpace ℝ (Fin 4))
    (((OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere a)).repr.symm z) : EuclideanSpace ℝ (Fin 4))
  rw [stereoInvFunAux_apply, smul_add]


noncomputable def threeSphereStereoMetric (a : UnitThreeSphere) :
    RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
  threeSphereMetric.pullbackOfLocalDiffeomorph (threeSphereStereoInverse a)
    (threeSphereStereoLocalDiffeomorph a)



theorem threeSphereStereoMetric_inner (a : UnitThreeSphere)
    (z u v : EuclideanSpace ℝ (Fin 3)) :
    (threeSphereStereoMetric a).inner z u v =
      (16 / (‖z‖ ^ 2 + 4) ^ 2) * inner ℝ u v := by
  let f := threeSphereStereoInverse a
  let inc : UnitThreeSphere → EuclideanSpace ℝ (Fin 4) := Subtype.val
  have hc : mfderiv (𝓡 3) (𝓡 4) (inc ∘ f) z =
      (mfderiv (𝓡 3) (𝓡 4) inc (f z)).comp (mfderiv (𝓡 3) (𝓡 3) f z) :=
    mfderiv_comp z ((contMDiff_coe_sphere (m := ∞) (f z)).mdifferentiableAt (by simp))
      ((threeSphereStereoLocalDiffeomorph a).contMDiff z |>.mdifferentiableAt (by simp))
  have he : inc ∘ f = fun y =>
      stereoInvFunAux (a : EuclideanSpace ℝ (Fin 4)) (sphereStereoPlane a y) :=
    funext (threeSphereStereoInverse_coe a)
  rw [he, mfderiv_eq_fderiv,
    (hasFDerivAt_stereo_comp_isometry a (sphereStereoPlane a) z).fderiv] at hc
  change threeSphereMetric.inner (f z)
    (mfderiv (𝓡 3) (𝓡 3) f z u) (mfderiv (𝓡 3) (𝓡 3) f z v) = _
  rw [threeSphereMetric_inner]
  change inner ℝ
    (((mfderiv (𝓡 3) (𝓡 4) inc (f z)).comp (mfderiv (𝓡 3) (𝓡 3) f z)) u)
    (((mfderiv (𝓡 3) (𝓡 4) inc (f z)).comp (mfderiv (𝓡 3) (𝓡 3) f z)) v) = _
  rw [← hc]
  exact stereoDifferential_inner a (sphereStereoPlane a) (sphereStereoPlane_orthogonal a) z u v

end PoincareConjecture.M38
