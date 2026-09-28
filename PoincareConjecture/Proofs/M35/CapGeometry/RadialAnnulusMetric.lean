import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialMetric
import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35

private theorem sphere_derivative_orthogonal (q : UnitTwoSphere)
    (v : TangentSpace (𝓡 2) q) :
    inner ℝ q.val (mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) q v) = 0 := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hmem : mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) q v ∈
      (mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) q).range := ⟨v, rfl⟩
  rw [range_mvfderiv_subtypeVal] at hmem
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem

theorem radial_annulus_coordinate_mfderiv (a b : ℝ)
    (z : StandardCylinderSpace) (v : RoundCylinderTangent z) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (fun y : StandardCylinderSpace => (a + b * y.2) • y.1.val) z v =
      (a + b * z.2) •
        mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) z.1 v.1 +
          (b * v.2) • z.1.val := by
  change EuclideanSpace ℝ (Fin 2) × ℝ at v
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let f : StandardCylinderSpace → ℝ := fun y => a + b * y.2
  let q : StandardCylinderSpace → StandardCapSpace := fun y => y.1.val
  have hf : HasMFDerivAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) f z
      (b • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ) := by
    simpa only [zero_add] using!
      (hasMFDerivAt_const (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) a z).add
        ((hasMFDerivAt_snd (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) z).const_smul b)
  have hq : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q z :=
    ((contMDiff_coe_sphere (m := ∞) (n := 2) (E := StandardCapSpace)).comp
      contMDiff_fst).mdifferentiable (by simp) z
  have hfd : mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) f z v = b * v.2 := by
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) f z v = _
    rw [hf.mfderiv]
    rfl
  have hqd : mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) q z v =
      mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) z.1 v.1 := by
    have h := mfderiv_comp_apply z
      ((contMDiff_coe_sphere (m := ∞) (n := 2) (E := StandardCapSpace)).mdifferentiable
        (by simp) z.1) (mdifferentiableAt_fst (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ))) v
    change @Eq StandardCapSpace _ _ at h
    rw [mfderiv_fst] at h
    exact h
  change mvfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (f • q) z v = _
  rw [mvfderiv_smul hf.mdifferentiableAt hq]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hfd, hqd, f, q]

namespace Uniqueness

variable (g : RiemannianMetric 3 StandardCapSpace)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : StandardCapSpace,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g)

theorem intrinsic_radial_annulus_pullback (a b : ℝ)
    (z : StandardCylinderSpace) (hz : 0 < a + b * z.2)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback (intrinsicSpatialMetric g hrotation hcomplete)
      (fun y : StandardCylinderSpace => (a + b * y.2) • y.1.val) z v w =
      intrinsicWarpingRadius g hrotation hcomplete (a + b * z.2) ^ 2 *
        inner ℝ
          (mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) z.1 v.1)
          (mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) z.1 w.1) +
        b ^ 2 * v.2 * w.2 := by
  let r := a + b * z.2
  have hnorm : ‖r • z.1.val‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hz, norm_eq_of_mem_sphere, mul_one]
  have hne : r • z.1.val ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne hz.ne')
  have hv := sphere_derivative_orthogonal z.1 v.1
  have hv' : inner ℝ (mvfderiv (𝓡 2) (fun p : UnitTwoSphere => p.val) z.1 v.1)
      z.1.val = 0 := (real_inner_comm _ _).trans hv
  have hw := sphere_derivative_orthogonal z.1 w.1
  have hunit : inner ℝ z.1.val z.1.val = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow]
  rw [roundCylinderPullback, radial_annulus_coordinate_mfderiv,
    radial_annulus_coordinate_mfderiv,
    intrinsicSpatialMetric_inner g hrotation hcomplete hne]
  rw [hnorm, ← mul_intrinsicWarpingQuotient g hrotation hcomplete r]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hv, hv', hw, hunit, mul_zero, add_zero, zero_add]
  field_simp [show r ≠ 0 from hz.ne']
  dsimp only [r]
  ring

end Uniqueness
end PoincareConjecture.M35
