import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.RadialBounds
import PoincareConjecture.Proofs.M34.Mathlib.RadialConnection
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.EuclideanConstruction











set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34



noncomputable def capChristoffelA (a r : ℝ) : ℝ :=
  deriv (capAngularCoefficient a) r / (2 * r * capAngularCoefficient a r)



noncomputable def capChristoffelB (a r : ℝ) : ℝ :=
  capRadialCoefficient a r - deriv (capAngularCoefficient a) r / (2 * r)



noncomputable def capChristoffelC (a r : ℝ) : ℝ :=
  deriv (capRadialCoefficient a) r / (2 * r) -
    2 * capChristoffelA a r * capRadialCoefficient a r



theorem capMetricInner_fderiv (a : ℝ) {x : StandardCapSpace} (hx : x ≠ 0)
    (u v w : StandardCapSpace) :
    fderiv ℝ (fun y => capMetricInner a y u v) x w =
      deriv (capAngularCoefficient a) ‖x‖ / ‖x‖ * inner ℝ x w * inner ℝ u v +
      deriv (capRadialCoefficient a) ‖x‖ / ‖x‖ * inner ℝ x w *
        (inner ℝ x u * inner ℝ x v) +
      capRadialCoefficient a ‖x‖ *
        (inner ℝ w u * inner ℝ x v + inner ℝ x u * inner ℝ w v) := by
  exact Poincare.fderiv_radial_pairing hx
    ((capAngularCoefficient_contDiffAt a (norm_ne_zero_iff.mpr hx)).differentiableAt
      (by simp)).hasDerivAt
    ((capRadialCoefficient_contDiffAt a (norm_ne_zero_iff.mpr hx)).differentiableAt
      (by simp)).hasDerivAt u v w



noncomputable def capLeviCivitaData (a : ℝ) (ha : 0 < a) (hapi : a ≤ Real.pi / 2) :
    LeviCivitaData (capRiemannianMetric a ha hapi) :=
  (capRiemannianMetric a ha hapi).euclideanLeviCivitaData

set_option backward.isDefEq.respectTransparency false in


theorem capConnection_formula {a : ℝ} (ha : 0 < a) (hapi : a ≤ Real.pi / 2)
    (D : LeviCivitaData (capRiemannianMetric a ha hapi))
    {x : StandardCapSpace} (hx : x ≠ 0) (u v : StandardCapSpace) :
    D.connection (fun _ => v) x u =
      Poincare.radialChristoffel (capChristoffelA a ‖x‖)
        (capChristoffelB a ‖x‖) (capChristoffelC a ‖x‖) x u v := by
  apply ((capRiemannianMetric a ha hapi).inner_isInvertible x).injective
  ext w
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc : capAngularCoefficient a ‖x‖ ≠ 0 :=
    (capAngularCoefficient_pos ha.le hapi (norm_nonneg x)).ne'
  have hr : capAngularCoefficient a ‖x‖ +
      capRadialCoefficient a ‖x‖ * ‖x‖ ^ 2 = 1 := by
    rw [capRadialCoefficient_mul_sq]
    ring
  have hA : 2 * capAngularCoefficient a ‖x‖ * capChristoffelA a ‖x‖ =
      deriv (capAngularCoefficient a) ‖x‖ / ‖x‖ := by
    unfold capChristoffelA
    field_simp
  have hB : 2 * capChristoffelB a ‖x‖ = 2 * capRadialCoefficient a ‖x‖ -
      deriv (capAngularCoefficient a) ‖x‖ / ‖x‖ := by
    unfold capChristoffelB
    ring
  have hC : 2 * (capChristoffelC a ‖x‖ +
      2 * capChristoffelA a ‖x‖ * capRadialCoefficient a ‖x‖) =
      deriv (capRadialCoefficient a) ‖x‖ / ‖x‖ := by
    unfold capChristoffelC
    ring
  have hk := D.inner_connection_const x u v w
  change 2 * capMetricInner a x (D.connection (fun _ => v) x u) w =
    fderiv ℝ (fun y => capMetricInner a y v w) x u +
    fderiv ℝ (fun y => capMetricInner a y w u) x v -
    fderiv ℝ (fun y => capMetricInner a y u v) x w at hk
  rw [capMetricInner_fderiv a hx, capMetricInner_fderiv a hx,
    capMetricInner_fderiv a hx] at hk
  have he := Poincare.radialChristoffel_koszul _ _ _ _ _ _ _ x u v w hr hA hB hC
  change capMetricInner a x (D.connection (fun _ => v) x u) w =
    capMetricInner a x _ w
  rw [capMetricInner_apply a x (Poincare.radialChristoffel _ _ _ x u v) w]
  linarith only [hk, he]

end PoincareConjecture.M34
