import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.CurvatureFormula
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.RadialGram

/-!
# Sectional numerator of the actual cap metric

Morgan-Tian Lemma 12.2, printed pp. 294-295. Pairing the genuine curvature
vector with the metric gives a radial squared norm and an angular Gram
determinant. This formula is valid for all fixed vectors, including
dependent ones, and uses the contract's actual curvature tensor.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M34

/-- Gram determinant of the cap metric, retaining the radial correction
(Lemma 12.2 curvature computation, pp. 294-295). -/
theorem capMetricInner_gram (a : ℝ) (x u v : StandardCapSpace) :
    capMetricInner a x u u * capMetricInner a x v v - capMetricInner a x u v ^ 2 =
      capAngularCoefficient a ‖x‖ ^ 2 *
        (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) +
      capAngularCoefficient a ‖x‖ * capRadialCoefficient a ‖x‖ *
        ‖inner ℝ x u • v - inner ℝ x v • u‖ ^ 2 := by
  exact Poincare.radial_pairing_gram _ _ x u v

set_option backward.isDefEq.respectTransparency false in
/-- The actual sectional numerator splits into radial and angular terms
at every nonzero point (Lemma 12.2, pp. 294-295). -/
theorem capCurvatureTensor_formula {a : ℝ} (ha : 0 < a) (hapi : a ≤ Real.pi / 2)
    (D : LeviCivitaData (capRiemannianMetric a ha hapi))
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    D.curvatureTensor x u v u v =
      (-capProfile a ‖x‖ * deriv (capSlope a) ‖x‖ / ‖x‖ ^ 4) *
        ‖inner ℝ x u • v - inner ℝ x v • u‖ ^ 2 +
      (capProfile a ‖x‖ ^ 2 * (1 - capSlope a ‖x‖ ^ 2) / ‖x‖ ^ 4) *
        (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 -
          ‖inner ℝ x u • v - inner ℝ x v • u‖ ^ 2 / ‖x‖ ^ 2) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hf : capProfile a ‖x‖ ≠ 0 :=
    (capProfile_pos ha.le hapi (norm_pos_iff.mpr hx)).ne'
  change capMetricInner a x (D.curvature x u v v) u = _
  rw [capCurvature_formula ha hapi D hx, capMetricInner_apply,
    Poincare.radial_cross_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm u v]
  rw [capRadialCoefficient, if_neg hr, capAngularCoefficient, if_neg hr]
  field_simp
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Spherical profile identities imply curvature one quarter times the
metric Gram determinant, before imposing orthonormality
(Lemma 12.2 round-tip computation, pp. 294-295). -/
theorem capCurvatureTensor_eq_quarter_of_profile {a : ℝ}
    (ha : 0 < a) (hapi : a ≤ Real.pi / 2)
    (D : LeviCivitaData (capRiemannianMetric a ha hapi))
    {x : StandardCapSpace} (hx : x ≠ 0)
    (hq : deriv (capSlope a) ‖x‖ = -capProfile a ‖x‖ / 4)
    (hp : capSlope a ‖x‖ ^ 2 = 1 - capProfile a ‖x‖ ^ 2 / 4)
    (u v : StandardCapSpace) :
    D.curvatureTensor x u v u v = (1 / 4 : ℝ) *
      (capMetricInner a x u u * capMetricInner a x v v - capMetricInner a x u v ^ 2) := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [capCurvatureTensor_formula ha hapi D hx, hq, hp, capMetricInner_gram,
    capRadialCoefficient, if_neg hr, capAngularCoefficient, if_neg hr]
  field_simp
  ring

end PoincareMT.M34
