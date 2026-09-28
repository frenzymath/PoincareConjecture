import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bilinear










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

open SpacetimeBounds



theorem ricciFlowOperator_metricTwoJet_apply {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    ricciFlowOperator n (metricTwoJet g.euclideanCoefficients x) u v =
      -2 * D.ricci x u v := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
      (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have hB (a c : EuclideanSpace ℝ (Fin n)) : B a c = D.ricci x a c := by
    simp only [B, LinearMap.sum_apply,
      LeviCivitaData.curvatureTensor_bilinear_first_third_apply, LeviCivitaData.ricci]
  have hexpand : B u v = ∑ i, ∑ j, inner ℝ (b i) u * inner ℝ (b j) v * B (b i) (b j) := by
    conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, OrthonormalBasis.repr_apply_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [ricciFlowOperator, jetRicci_metricTwoJet D, ← hB,
    sum_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [hexpand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [b]
  ring

end PoincareConjecture.M34
