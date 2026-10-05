import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Volume.ModelVolume
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.UniformConstants

/-!
# A radius-independent loss for smaller noncollapsed balls

Morgan--Tian Theorem 1.34, p. 19, applied in the small-radius case of
Proposition 16.1, pp. 367-368. On a radius-R ball with curvature at most
R^-2, the model profile lies between t and cosh(1)*t. The resulting
three-dimensional volume loss is independent of R and of the flow.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.M15
export PoincareMT.Generalized.Noncollapse (calibratedMetricVolume_eq_volumeMeasure)
end PoincareMT.M15

namespace PoincareMT.Proofs.M46

/-- The fixed Bishop--Gromov loss is chosen before any surgery scale. -/
noncomputable def smallBallLoss : ℝ := (Real.cosh 1)⁻¹ ^ 2

/-- The fixed comparison loss leaves a positive noncollapse constant. -/
theorem smallBallLoss_pos : 0 < smallBallLoss := by
  exact pow_pos (inv_pos.mpr (Real.cosh_pos 1)) _

/-- The derivative of sinh is bounded by cosh(1) on the unit interval. -/
theorem sinh_le_cosh_one_mul {z : ℝ} (hz : z ∈ Icc 0 1) :
    Real.sinh z ≤ Real.cosh 1 * z := sinh_le_cosh_mul hz

/-- The normalized hyperbolic radial profile has a uniform upper bound. -/
theorem modelS_inv_sq_le {R t : ℝ} (hR : 0 < R) (ht : t ∈ Icc 0 R) :
    RiemannianMetric.modelS (R⁻¹ ^ 2) t ≤ Real.cosh 1 * t := by
  simpa only [one_div] using modelS_scaled_inv_sq_le (by norm_num : (0 : ℝ) < 1) hR ht

/-- The model ball of radius R is at most cosh(1)^2 times Euclidean volume. -/
theorem modelVolume_inv_sq_le {R : ℝ} (hR : 0 < R) :
    RiemannianMetric.modelVolume 3 (R⁻¹ ^ 2) R ≤
      Real.cosh 1 ^ 2 * RiemannianMetric.euclideanUnitBallVolume 3 * R ^ 3 := by
  simpa only [one_div] using modelVolume_scaled_inv_sq_le (by norm_num : (0 : ℝ) < 1) hR

/-- The radius-dependent comparison ratio retains a fixed cubic constant. -/
theorem smallBallVolumeBound_ge {R s k : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hk : 0 < k) :
    smallBallLoss * k * s ^ 3 ≤
      RiemannianMetric.smallerBallVolumeBound 3 (R⁻¹ ^ 2) R (k * R ^ 3) s := by
  simpa only [smallBallLoss, one_div] using
    scaled_smallBallVolumeBound_ge (by norm_num : (0 : ℝ) < 1) hR hs hk

/-- An actual controlled larger ball gives cubic volume at all smaller
radii, with the same fixed loss on every metric and every scale. -/
theorem calibrated_small_ball_lower_bound
    {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (p : M)
    {R s k : ℝ} (hR : 0 < R) (hs : 0 < s) (hsR : s ≤ R) (hk : 0 < k)
    (hcompact : IsCompact (closure (g.ball p (2 * R))))
    (hcurv : ∀ x ∈ g.ball p (2 * R), D.curvatureTensorNorm x ≤ R⁻¹ ^ 2)
    (hvolume : ENNReal.ofReal (k * R ^ 3) ≤ calibratedMetricVolume g (g.ball p R)) :
    ENNReal.ofReal (smallBallLoss * k * s ^ 3) ≤
      calibratedMetricVolume g (g.ball p s) := by
  rw [M15.calibratedMetricVolume_eq_volumeMeasure] at hvolume ⊢
  have hbound := (g.smallerBall_volume_lower_bound_of_curvatureTensorNorm_le D p
    (by norm_num) (sq_nonneg R⁻¹) hR (mul_pos hk (pow_pos hR 3))
    hcompact hcurv hvolume hs hsR).2
  exact (ENNReal.ofReal_le_ofReal (smallBallVolumeBound_ge hR hs hk)).trans hbound

/-- Absorb the smaller-ball and canonical losses before choosing rNext.
The source time, length and volume parameters are unchanged. -/
noncomputable def smallRadiusUniformData {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (kCan : ℝ) (hkCan : 0 < kCan) : M15GeneralizedUniformData.{u} 3 taubar l0 V :=
  canonicalUniformData U (min kCan (smallBallLoss * configurationKappa p U))
    (lt_min hkCan (mul_pos smallBallLoss_pos (configurationKappa_pos p U)))

/-- The final constant includes the larger-test volume and comparison loss. -/
theorem smallRadiusUniformData_le_small_ball {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (kCan : ℝ) (hkCan : 0 < kCan) :
    configurationKappa p (smallRadiusUniformData p U kCan hkCan) ≤
      smallBallLoss * configurationKappa p U :=
  (configurationKappa_le_canonical p U _ _).trans (min_le_right _ _)

/-- The same final constant also works in the canonical-neighborhood case. -/
theorem smallRadiusUniformData_le_canonical {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {taubar l0 V : ℝ}
    (U : M15GeneralizedUniformData.{u} 3 taubar l0 V)
    (kCan : ℝ) (hkCan : 0 < kCan) :
    configurationKappa p (smallRadiusUniformData p U kCan hkCan) ≤ kCan :=
  (configurationKappa_le_canonical p U _ _).trans (min_le_left _ _)

end PoincareMT.Proofs.M46
