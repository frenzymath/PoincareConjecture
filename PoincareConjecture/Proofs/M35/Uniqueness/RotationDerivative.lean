import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoordinateOperator
import PoincareConjecture.Proofs.M35.CapGeometry.RadialEndSlope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

theorem rotational_connection_linear_skew
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (B : StandardCapSpace →L[ℝ] StandardCapSpace)
    (hskew : ∀ x, inner ℝ x (B x) = 0)
    {x : StandardCapSpace} (hx : x ≠ 0) (u : StandardCapSpace) :
    D.connection (fun y => B y) x u = B u +
      (radialConnectionAlpha g ‖x‖ * inner ℝ x u) • B x +
      (radialConnectionBeta g ‖x‖ * inner ℝ u (B x)) • x := by
  rw [D.connection_eq_fderiv_add B.differentiableAt u, B.fderiv]
  change @Add.add StandardCapSpace inferInstance (B u)
    (D.connection (fun _ : StandardCapSpace => B x) x u) = _
  rw [rotational_connection_const D hrotation hx u (B x), hskew x]
  simp only [zero_smul, add_zero, mul_zero, smul_smul]
  exact (add_assoc (B u) _ _).symm

theorem radialConnection_beta_identity
    (g : RiemannianMetric 3 StandardCapSpace) {r : ℝ} (hr : 0 < r) :
    axisRadialCoefficient g r * (1 - r ^ 2 * radialConnectionBeta g r) =
      axisAngularCoefficient g r * (1 + r ^ 2 * radialConnectionAlpha g r) := by
  unfold radialConnectionBeta radialConnectionAlpha axisCorrectionCoefficient
  field_simp [(axisAngularCoefficient_pos g r).ne',
    (axisRadialCoefficient_pos g r).ne', hr.ne']
  ring

theorem radialConnection_alpha_weighted_bound
    {g : RiemannianMetric 3 StandardCapSpace} (D : LeviCivitaData g)
    (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      ∀ x u v : StandardCapSpace,
        g.inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
    (hsec : D.NonnegativeSectionalCurvature) (hcomplete : MetricComplete g)
    {r : ℝ} (hr : 0 < r) :
    axisAngularCoefficient g r * (1 + r ^ 2 * radialConnectionAlpha g r) ^ 2 ≤
      axisRadialCoefficient g r := by
  have hlo := axisWarpingSlope_nonneg D hrotation hsec hcomplete hr
  have hhi := axisWarpingSlope_le_one D hrotation hsec hr
  have hs : axisWarpingSlope g r ^ 2 ≤ 1 := by nlinarith only [hlo, hhi]
  rw [axisWarpingSlope, axisRadialSpeed, div_pow, mul_pow,
    Real.sq_sqrt (axisAngularCoefficient_pos g r).le,
    Real.sq_sqrt (axisRadialCoefficient_pos g r).le] at hs
  exact (div_le_one (axisRadialCoefficient_pos g r)).mp hs

end PoincareConjecture.M35.Uniqueness
