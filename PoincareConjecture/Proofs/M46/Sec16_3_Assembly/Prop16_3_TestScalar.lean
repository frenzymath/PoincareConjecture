import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_4_RegularRegion
import PoincareConjecture.Proofs.M10.ScalarBound









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M46



theorem NoncollapseTest.terminal_curvature {F : SurgeryFlowData.{u}}
    {O : SurgeryObservation F} (D : NoncollapseTest F O)
    {y : (F.slice D.time).carrier} (hy : y ∈ (F.metric D.time).ball D.center D.radius) :
    (F.connection D.time).curvatureTensorNorm y ≤ D.radius⁻¹ ^ 2 := by
  have hzero : (0 : ℝ) ∈ Icc (-D.radius ^ 2) 0 := ⟨by nlinarith [sq_nonneg D.radius], le_rfl⟩
  have h := D.curvature 0 hzero y hy
  have hp : (⟨D.time + 0 / 1, D.cylinder.forward 0 hzero y⟩ :
      (t : ℝ) × (F.slice t).carrier) = ⟨D.time, y⟩ :=
    Sigma.ext (by simp) (D.based hzero y hy)
  have hnorm := congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
    (F.connection p.1).curvatureTensorNorm p.2) hp
  exact hnorm ▸ h


theorem NoncollapseTest.center_scalar_le {F : SurgeryFlowData.{u}}
    {O : SurgeryObservation F} (D : NoncollapseTest F O) :
    (F.connection D.time).scalarCurvature D.center ≤ 9 * D.radius⁻¹ ^ 2 := by
  have hcenter : D.center ∈ (F.metric D.time).ball D.center D.radius := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice D.time).carrier → Type _) :=
      ⟨(F.metric D.time).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) D.center D.center < ENNReal.ofReal D.radius
    simpa only [Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr D.radius_pos
  have htrace := (le_abs_self _).trans
    (M10.abs_scalarCurvature_le (F.metric D.time) (F.connection D.time) D.center)
  norm_num only [Nat.cast_ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at htrace
  exact htrace.trans (mul_le_mul_of_nonneg_left (D.terminal_curvature hcenter) (by norm_num))



theorem canonicalNeck_scale_of_scalar_bound
    {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) {s : ℝ} (hs : 0 < s)
    (hscalar : N.connection.scalarCurvature N.center ≤ 9 * s⁻¹ ^ 2) :
    s ≤ 3 * N.scale := by
  have hscale := N.scale_pos
  have hnormalize : N.scale⁻¹ ^ 2 = N.connection.scalarCurvature N.center := by
    rw [N.scale_eq_scalar, inv_pow,
      ← Real.rpow_mul_natCast N.scalar_center_pos.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  rw [← hnormalize] at hscalar
  have hscaled := mul_le_mul_of_nonneg_right hscalar (sq_nonneg (s * N.scale))
  field_simp [hs.ne', hscale.ne'] at hscaled
  nlinarith

end PoincareConjecture.Proofs.M46
