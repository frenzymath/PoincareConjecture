import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Patches
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_LocalScalarTransport









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45NeckGluingInput

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)

set_option backward.isDefEq.respectTransparency false in


theorem identify_mfderiv_invertible (x : I.recent_carrier.carrier)
    (hx : x ∈ I.recent_patch.carrier) :
    (mfderiv (𝓡 3) (𝓡 3) I.identify x).IsInvertible := by
  have hb := (I.recent_flow.metric (-I.recent_duration)).mfderiv_bijective_of_pullback_eq
    (I.older_flow.metric (-I.recent_duration)) x (I.joining_metric x hx)
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) I.identify x
  exact ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hb.1)
    (LinearMap.range_eq_top.mpr hb.2), rfl⟩



theorem joining_scalar_eq :
    I.older_neck.neck.connection.scalarCurvature I.older_neck.neck.center =
      (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center := by
  have h := M44.scalar_ricciNormSq_eq_of_local_isometry
    (I.recent_flow.connection (-I.recent_duration))
    (I.older_flow.connection (-I.recent_duration))
    I.recent_patch.carrier_open I.identify_smooth (I.identify_mfderiv_invertible)
    (fun x hx v w => (I.joining_metric x hx v w).symm) I.recent_patch.center_mem
  simpa only [I.identify_center, I.older_neck.connection_eq] using h.1




theorem older_scale_sq :
    I.older_neck.neck.scale ^ 2 =
      ((I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center)⁻¹ := by
  rw [I.older_neck.neck.scale_eq_scalar,
    ← Real.rpow_mul_natCast I.older_neck.neck.scalar_center_pos.le (-1 / 2) 2]
  norm_num only [show (-1 / 2 : ℝ) * (2 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
  rw [I.joining_scalar_eq]



theorem older_survival_of_joining_scalar
    (hscalar : (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center ≤ 1) :
    ∀ t ∈ Set.Ioc (-1 : ℝ) 0, t < -I.recent_duration →
      t ∈ Set.Ioc (-I.older_duration) (-I.recent_duration) := by
  have hpos : 0 < (I.recent_flow.connection (-I.recent_duration)).scalarCurvature I.center := by
    rw [← I.joining_scalar_eq]
    exact I.older_neck.neck.scalar_center_pos
  apply I.older_survival_of_scale
  rw [I.older_scale_sq]
  simpa only [inv_one] using inv_anti₀ hpos hscalar

end PoincareConjecture.M45NeckGluingInput
