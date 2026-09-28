import PoincareConjecture.Proofs.M35.CapGeometry.RadialAnnulusComparison
import PoincareConjecture.Proofs.M35.CapGeometry.TerminalCap.AngularRadius

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem radialArclength_scale (g : RiemannianMetric 3 StandardCapSpace)
    (Q : ℝ) (hQ : 0 < Q) (r : ℝ) :
    radialArclength (M13.scaleSmoothMetric g Q hQ) r =
      Real.sqrt Q * radialArclength g r := by
  change (∫ s in (0 : ℝ)..r, axisRadialSpeed (M13.scaleSmoothMetric g Q hQ) s) =
    Real.sqrt Q * ∫ s in (0 : ℝ)..r, axisRadialSpeed g s
  simp_rw [axisRadialSpeed_scale]
  exact intervalIntegral.integral_const_mul _ _

theorem intrinsicWarpingRadius_scale (g : RiemannianMetric 3 StandardCapSpace)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hcomplete : MetricComplete g) (Q : ℝ) (hQ : 0 < Q) (s : ℝ) :
    intrinsicWarpingRadius (M13.scaleSmoothMetric g Q hQ)
      (scaleSmoothMetric_rotation_invariant hrotation Q hQ)
      (scaleSmoothMetric_complete g hcomplete Q hQ) s =
      Real.sqrt Q * intrinsicWarpingRadius g hrotation hcomplete (s / Real.sqrt Q) := by
  let G := M13.scaleSmoothMetric g Q hQ
  let hrot := scaleSmoothMetric_rotation_invariant hrotation Q hQ
  let hc := scaleSmoothMetric_complete g hcomplete Q hQ
  let R := radialArclengthOrderIso g hrotation hcomplete
  let S := radialArclengthOrderIso G hrot hc
  have hinverse : S.symm s = R.symm (s / Real.sqrt Q) := by
    apply S.injective
    rw [OrderIso.apply_symm_apply]
    change s = radialArclength (M13.scaleSmoothMetric g Q hQ)
      (R.symm (s / Real.sqrt Q))
    rw [radialArclength_scale]
    change s = Real.sqrt Q * R (R.symm (s / Real.sqrt Q))
    rw [OrderIso.apply_symm_apply]
    field_simp [(Real.sqrt_pos.mpr hQ).ne']
  change axisWarpingRadius G (S.symm s) = _
  rw [hinverse, axisWarpingRadius_scale]
  rfl

end PoincareConjecture.M35.Uniqueness

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

theorem RadialAnnulusComparison.original {g₀ : StandardInitialMetric}
    {E : RepairedStandardCapExistenceData g₀} {t : ℝ}
    {ht : t ∈ Ico 0 E.flow.base.lifetime} {x : StandardCapSpace} {epsilon : ℝ}
    (h : RadialAnnulusComparison E t ht x epsilon) :
    let Q := (E.flow.connection t).scalarCurvature x
    let b := (Real.sqrt Q)⁻¹
    let a := radialArclength (E.flow.metric t) ‖x‖
    0 < a - b * epsilon⁻¹ ∧ RoundCylinderClose epsilon 0
      (radialCylinderTensor (fun u => Q * intrinsicWarpingRadius (E.flow.metric t)
        (E.rotation_invariant t ht) (E.complete t ht) (a + b * u) ^ 2) 1) := by
  let g := E.flow.metric t
  let Q := (E.flow.connection t).scalarCurvature x
  let hQ := E.scalar_pos ht x
  let G := M13.scaleSmoothMetric g Q hQ
  let hrot := scaleSmoothMetric_rotation_invariant (E.rotation_invariant t ht) Q hQ
  let hc := scaleSmoothMetric_complete g (E.complete t ht) Q hQ
  let a := radialArclength g ‖x‖
  let b := (Real.sqrt Q)⁻¹
  change 0 < a - b * epsilon⁻¹ ∧ _
  change 0 < radialArclength G ‖x‖ - epsilon⁻¹ ∧ _ at h
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hinner : 0 < a - b * epsilon⁻¹ := by
    have hi := h.1
    rw [radialArclength_scale] at hi
    have hid : Real.sqrt Q * (a - b * epsilon⁻¹) =
        Real.sqrt Q * a - epsilon⁻¹ := by
      dsimp only [b]
      field_simp [hsqrt.ne']
    apply (mul_pos_iff_of_pos_left hsqrt).mp
    rw [hid]
    exact hi
  refine ⟨hinner, ?_⟩
  have heq : (fun u => intrinsicWarpingRadius G hrot hc
      (radialArclength G ‖x‖ + u) ^ 2) =
      (fun u => Q * intrinsicWarpingRadius g (E.rotation_invariant t ht)
        (E.complete t ht) (a + b * u) ^ 2) := by
    funext u
    rw [intrinsicWarpingRadius_scale g (E.rotation_invariant t ht) (E.complete t ht),
      radialArclength_scale, mul_pow, Real.sq_sqrt hQ.le]
    congr 2
    dsimp only [a, b]
    field_simp [hsqrt.ne']
  rw [← heq]
  exact h.2

theorem RadialAnnulusComparison.radius_bound {g₀ : StandardInitialMetric}
    {E : RepairedStandardCapExistenceData g₀} {t : ℝ}
    {ht : t ∈ Ico 0 E.flow.base.lifetime} {x : StandardCapSpace} {epsilon : ℝ}
    (he : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (h : RadialAnnulusComparison E t ht x epsilon) :
    (E.flow.connection t).scalarCurvature x *
      intrinsicWarpingRadius (E.flow.metric t) (E.rotation_invariant t ht)
        (E.complete t ht) (radialArclength (E.flow.metric t) ‖x‖) ^ 2 < 4 := by
  simpa only [mul_zero, add_zero] using
    radialCylinderTensor_angular_lt_four he hehalf h.original.2

end PoincareConjecture.M35.OrdinaryRealization
