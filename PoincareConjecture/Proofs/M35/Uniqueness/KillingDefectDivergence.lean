import PoincareConjecture.Proofs.M35.Uniqueness.KillingDefectTensor
import PoincareConjecture.Proofs.M35.Uniqueness.KillingStationary
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Linearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

local notation:max "V" n:max => EuclideanSpace ℝ (Fin n)

theorem killingDefectTensor_derivative {n : ℕ} {g : RiemannianMetric n (V n)}
    (D : LeviCivitaData g) (X : V n → V n) (hX : ContDiff ℝ ∞ X)
    (x : V n) (v : Fin 3 → V n) :
    D.covariantTensorDerivative (killingDefectTensor D X) x v =
      g.inner x (fieldHessian D X x (v 0) (v 1)) (v 2) +
        g.inner x (fieldHessian D X x (v 0) (v 2)) (v 1) := by
  let K := D.covariantTensorDerivative (killingCovector g X)
  let σ := Equiv.swap (0 : Fin 2) 1
  have hK := M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (isSmoothCovariantTensor_killingCovector g X hX)
  have hdef : killingDefectTensor D X = fun y w => K y w + M04.tensorPermute K σ y w := by
    funext y w
    have hw : ![w 0, w 1] = w := by ext i; fin_cases i <;> rfl
    have hp : w ∘ σ = ![w 1, w 0] := by ext i; fin_cases i <;> simp [σ]
    change DeTurckNative.metricLieDerivative D X y (w 0) (w 1) = _
    rw [killing_defect_eq_covector_symmetrization D X hX, M04.tensorPermute, hp, hw]
  have hp : D.covariantTensorDerivative (M04.tensorPermute K σ) x v =
      D.covariantTensorDerivative K x ![v 0, v 2, v 1] := by
    change D.covariantTensorDerivative (fun y w => K y (w ∘ σ)) x v = _
    rw [D.covariantTensorDerivative_reindex]
    congr 1
    ext i
    fin_cases i
    · rfl
    · change v (((Equiv.swap (0 : Fin 2) 1) 0).succ) = v 2
      rw [Equiv.swap_apply_left]
      rfl
    · change v (((Equiv.swap (0 : Fin 2) 1) 1).succ) = v 1
      rw [Equiv.swap_apply_right]
      rfl
  rw [hdef, D.covariantTensorDerivative_add hK (M04.isSmoothCovariantTensor_tensorPermute hK σ)]
  change D.covariantTensorDerivative K x v +
    D.covariantTensorDerivative (M04.tensorPermute K σ) x v = _
  rw [hp]
  change D.covariantTensorDerivative (D.covariantTensorDerivative (killingCovector g X)) x v +
    D.covariantTensorDerivative (D.covariantTensorDerivative (killingCovector g X)) x
      ![v 0, v 2, v 1] = _
  rw [killingCovector_second_derivative D X hX, killingCovector_second_derivative D X hX]
  rfl

theorem vector_heat_pair_eq_defect_derivative_trace {n : ℕ}
    {g : RiemannianMetric n (V n)} (D : LeviCivitaData g)
    (X : V n → V n) (hX : ContDiff ℝ ∞ X) (x w : V n) :
    g.inner x (@Add.add (V n) inferInstance
      (∑ i, fieldHessian D X x (g.orthonormalBasis x i) (g.orthonormalBasis x i))
      (RicciFlow.ricciSharp D x (X x))) w =
      (∑ i, D.covariantTensorDerivative (killingDefectTensor D X) x
        ![g.orthonormalBasis x i, g.orthonormalBasis x i, w]) -
      (1 / 2 : ℝ) * ∑ i, D.covariantTensorDerivative (killingDefectTensor D X) x
        ![w, g.orthonormalBasis x i, g.orthonormalBasis x i] := by
  classical
  have hcurv (e : V n) :
      g.inner x (D.curvature x w e e) (X x) =
        g.inner x (D.curvature x e w (X x)) e := by
    rw [Proofs.M03.curvature_pair_skew D x w e e (X x)]
    have hs : D.curvature x w e (X x) = -D.curvature x e w (X x) :=
      Proofs.M03.curvatureOnFields_swap D _ _ _ x
    rw [hs, map_neg, neg_neg, g.symm]
  have hterm (e : V n) :
      g.inner x (fieldHessian D X x e e) w + g.inner x (D.curvature x w e e) (X x) =
        D.covariantTensorDerivative (killingDefectTensor D X) x ![e, e, w] -
        (1 / 2 : ℝ) * D.covariantTensorDerivative (killingDefectTensor D X) x ![w, e, e] := by
    rw [hcurv, killingDefectTensor_derivative D X hX, killingDefectTensor_derivative D X hX]
    have hc := congrArg (fun z => g.inner x z e) (fieldHessian_commutator D X hX x e w)
    simp only [map_sub, sub_apply] at hc
    change g.inner x (fieldHessian D X x e e) w +
      g.inner x (D.curvature x e w (X x)) e =
      g.inner x (fieldHessian D X x e e) w + g.inner x (fieldHessian D X x e w) e -
      (1 / 2 : ℝ) * (g.inner x (fieldHessian D X x w e) e +
        g.inner x (fieldHessian D X x w e) e)
    linarith only [hc]
  calc
    _ = g.inner x (∑ i, fieldHessian D X x
          (g.orthonormalBasis x i) (g.orthonormalBasis x i)) w + D.ricci x w (X x) := by
      rw [show g.inner x (@Add.add (V n) inferInstance _ _) w =
        g.inner x (∑ i, fieldHessian D X x (g.orthonormalBasis x i)
          (g.orthonormalBasis x i)) w +
        g.inner x (RicciFlow.ricciSharp D x (X x)) w from
          congrArg (fun L => L w) ((g.euclideanCoefficients x).map_add _ _)]
      rw [inner_ricciSharp]
    _ = _ := by
      simp only [map_sum, sum_apply, LeviCivitaData.ricci, LeviCivitaData.curvatureTensor,
        ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hterm (g.orthonormalBasis x i))

end PoincareConjecture.M35.Uniqueness
