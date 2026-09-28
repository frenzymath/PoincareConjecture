import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Sectional









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Poincare.Geometry.Curvature.Hypersurface
open scoped ContDiff Manifold Bundle Topology

namespace PoincareConjecture.RiemannianMetric.FactorCurvature

variable {n : ℕ}
  {g : RiemannianMetric (n + 1) (EuclideanSpace ℝ (Fin (n + 1)))}
  {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem secondFundamentalForm_eq_zero_of_parallel_normal
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {F ν : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1))}
    {x : EuclideanSpace ℝ (Fin n)}
    (hF : ContDiffAt ℝ ∞ F x) (hν : DifferentiableAt ℝ ν x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (hunit : g.inner (F x) (ν x) (ν x) = 1)
    (horth : ∀ᶠ y in 𝓝 x, ∀ a, g.inner (F y) (ν y) (fderiv ℝ F y a) = 0)
    (hparallel : ∀ a, covariantDerivativeAlongMap D F ν x a = 0)
    (u v : EuclideanSpace ℝ (Fin n)) : secondFundamentalForm D Dh F x u v = 0 := by
  have hn := inner_shapeOperator_neg_normal_eq_normal_derivative D Dh hF hν horth u v
  rw [hparallel, inner_shapeOperator] at hn
  simp only [map_neg, neg_apply, map_zero, zero_apply] at hn
  have hn' : g.inner (F x) (secondFundamentalForm D Dh F x u v) (ν x) = 0 := by
    rw [g.symm]
    linarith
  have hs := metric_inner_normals_eq_mul g (F x) (fderiv ℝ F x).toLinearMap
    (fderiv_injective_of_pullback_metric hmetric.self_of_nhds) (ν x) hunit
    horth.self_of_nhds (secondFundamentalForm D Dh F x u v)
    (secondFundamentalForm D Dh F x u v) (secondFundamentalForm_normal D Dh hF hmetric u v)
  rw [hn', zero_mul] at hs
  by_contra hne
  exact (ne_of_gt (g.pos (F x) _ hne)) hs



theorem curvatureTensor_eq_of_parallel_normal
    (D : LeviCivitaData g) (Dh : LeviCivitaData h)
    {F ν : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1))}
    {x : EuclideanSpace ℝ (Fin n)}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y) (hν : DifferentiableAt ℝ ν x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (hunit : g.inner (F x) (ν x) (ν x) = 1)
    (horth : ∀ᶠ y in 𝓝 x, ∀ a, g.inner (F y) (ν y) (fderiv ℝ F y a) = 0)
    (hparallel : ∀ a, covariantDerivativeAlongMap D F ν x a = 0)
    (u v w z : EuclideanSpace ℝ (Fin n)) :
    Dh.curvatureTensor x u v w z = D.curvatureTensor (F x)
      (fderiv ℝ F x u) (fderiv ℝ F x v) (fderiv ℝ F x w) (fderiv ℝ F x z) := by
  rw [gauss_curvatureTensor_of_eventually D Dh hF hmetric]
  simp only [secondFundamentalForm_eq_zero_of_parallel_normal D Dh hF.self_of_nhds hν
    hmetric hunit horth hparallel, map_zero, add_zero, sub_zero]

end PoincareConjecture.RiemannianMetric.FactorCurvature
