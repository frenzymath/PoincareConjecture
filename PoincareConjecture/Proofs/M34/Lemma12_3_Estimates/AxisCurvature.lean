import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.CurvatureCoefficients
import PoincareConjecture.Proofs.M34.Mathlib.RadialConnectionDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean

set_option autoImplicit false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

set_option backward.isDefEq.respectTransparency false in

theorem initialCurvature_formula (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) (u v w : StandardCapSpace) :
    let A := initialChristoffelA g₀ ‖x‖
    let B := initialChristoffelB g₀ ‖x‖
    let C := initialChristoffelC g₀ ‖x‖
    g₀.connection.curvature x u v w =
      (B - A + A * B * ‖x‖ ^ 2) • (inner ℝ v w • u - inner ℝ u w • v) +
      ((C - deriv (initialChristoffelA g₀) ‖x‖ / ‖x‖ + A ^ 2 + A * C * ‖x‖ ^ 2) *
        inner ℝ x w) • (inner ℝ x v • u - inner ℝ x u • v) +
      ((deriv (initialChristoffelB g₀) ‖x‖ / ‖x‖ - C + B ^ 2 + B * C * ‖x‖ ^ 2) *
        (inner ℝ x u * inner ℝ v w - inner ℝ x v * inner ℝ u w)) • x := by
  dsimp only
  have he (p q : StandardCapSpace) : g₀.connection.euclideanConnection p q =ᶠ[𝓝 x]
      (fun y => Poincare.radialChristoffel (initialChristoffelA g₀ ‖y‖)
        (initialChristoffelB g₀ ‖y‖) (initialChristoffelC g₀ ‖y‖) y p q) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact initialConnection_formula g₀ hy p q
  have hp (p q : StandardCapSpace) : g₀.connection.euclideanConnection p q x =
      Poincare.radialChristoffel (initialChristoffelA g₀ ‖x‖)
        (initialChristoffelB g₀ ‖x‖) (initialChristoffelC g₀ ‖x‖) x p q :=
    initialConnection_formula g₀ hx p q
  rw [g₀.connection.curvature_eq_euclideanConnection,
    (he v w).fderiv_eq, (he u w).fderiv_eq]
  simp only [hp]
  obtain ⟨hA, hB, hC⟩ := initialChristoffel_contDiffAt g₀ (norm_ne_zero_iff.mpr hx)
  exact Poincare.radialChristoffel_curvature_expression hx
    (hA.differentiableAt (by simp)).hasDerivAt
    (hB.differentiableAt (by simp)).hasDerivAt
    (hC.differentiableAt (by simp)).hasDerivAt u v w

set_option backward.isDefEq.respectTransparency false in

theorem initialCurvature_angular_axis (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    g₀.connection.curvature (EuclideanSpace.single (0 : Fin 3) r)
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
    ((1 - initialWeightedSlope g₀ r ^ 2) / r ^ 2) •
      EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
  have hx : EuclideanSpace.single (0 : Fin 3) r ≠ (0 : StandardCapSpace) := by
    simp [hr.ne']
  rw [initialCurvature_formula g₀ hx]
  simp only [EuclideanSpace.inner_single_right, PiLp.norm_single,
    Real.norm_eq_abs, abs_of_pos hr]
  norm_num
  rw [initialCurvature_coefficient_F g₀ hr]
  simp

set_option backward.isDefEq.respectTransparency false in

theorem initialCurvature_radial_axis (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    g₀.connection.curvature (EuclideanSpace.single (0 : Fin 3) r)
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) =
    (-initialWarping g₀ r * deriv (initialWeightedSlope g₀) r /
        (initialRadialSpeed g₀ r * r ^ 2)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  have hx : EuclideanSpace.single (0 : Fin 3) r ≠ (0 : StandardCapSpace) := by
    simp [hr.ne']
  rw [initialCurvature_formula g₀ hx]
  simp only [EuclideanSpace.inner_single_right, PiLp.norm_single,
    Real.norm_eq_abs, abs_of_pos hr]
  norm_num
  have haxis : EuclideanSpace.single (0 : Fin 3) r =
      r • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by ext i; simp
  rw [haxis, smul_smul, ← add_smul]
  congr 1
  convert! initialCurvature_coefficient_radial g₀ hr using 1 <;> ring

set_option backward.isDefEq.respectTransparency false in

theorem initialCurvatureTensor_angular_axis (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    g₀.connection.curvatureTensor (EuclideanSpace.single (0 : Fin 3) r)
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      initialAngularCoefficient g₀ r * (1 - initialWeightedSlope g₀ r ^ 2) / r ^ 2 := by
  change g₀.metric.inner _ (g₀.connection.curvature _ _ _ _) _ = _
  rw [initialCurvature_angular_axis g₀ hr]
  simp only [map_smul, smul_apply, smul_eq_mul]
  change (1 - initialWeightedSlope g₀ r ^ 2) / r ^ 2 * initialAngularCoefficient g₀ r = _
  ring

set_option backward.isDefEq.respectTransparency false in

theorem initialCurvatureTensor_radial_axis (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 < r) :
    g₀.connection.curvatureTensor (EuclideanSpace.single (0 : Fin 3) r)
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) =
      -(initialRadialSpeed g₀ r * initialWarping g₀ r / r ^ 2) *
        deriv (initialWeightedSlope g₀) r := by
  have ha := (initialRadialSpeed_pos g₀ r).ne'
  change g₀.metric.inner _ (g₀.connection.curvature _ _ _ _) _ = _
  rw [initialCurvature_radial_axis g₀ hr]
  simp only [map_smul, smul_apply, smul_eq_mul]
  change (-initialWarping g₀ r * deriv (initialWeightedSlope g₀) r /
    (initialRadialSpeed g₀ r * r ^ 2)) * initialRadialCoefficient g₀ r = _
  rw [initialRadialCoefficient_eq]
  field_simp

end PoincareConjecture.M34
