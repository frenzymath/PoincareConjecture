import PoincareConjecture.Proofs.M36.ComparisonCovariantJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Jacobi.Coefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Linearity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open M36 CoordinateExponential

local notation "E" => EuclideanSpace ℝ (Fin 3)




noncomputable def connectionDifference (g h : RiemannianMetric 3 E) (x : E) :
    E →L[ℝ] E →L[ℝ] E :=
  christoffelBilinear h.euclideanCoefficients x -
    christoffelBilinear g.euclideanCoefficients x



noncomputable def metricError (g h : RiemannianMetric 3 E) :
    CovariantTensorEvaluation 3 E 2 :=
  fun x v => h.inner x (v 0) (v 1) - g.inner x (v 0) (v 1)



theorem metricError_isSmooth (g h : RiemannianMetric 3 E) :
    IsSmoothCovariantTensor (metricError g h) :=
  (isSmoothCovariantTensor_metric h).sub (isSmoothCovariantTensor_metric g)




theorem fderiv_bilinear_eq_covariant {g : RiemannianMetric 3 E}
    (D : LeviCivitaData g) {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ContDiff ℝ ∞ B) (x u v w : E) :
    fderiv ℝ (fun y => B y v w) x u =
      D.covariantTensorDerivative (k := 2) (fun y a => B y (a 0) (a 1)) x ![u, v, w] +
        B x (christoffelBilinear g.euclideanCoefficients x u v) w +
        B x v (christoffelBilinear g.euclideanCoefficients x u w) := by
  have hh := D.fderiv_covariantTensor_pullback_model (comparison_bilinear_isSmooth hB)
    (q := id) (V := fun i (_ : E) => (![v, w] : Fin 2 → E) i) (p := x)
    differentiableAt_id (fun i => differentiableAt_const ((![v, w] : Fin 2 → E) i)) u
  simpa [id_eq, LeviCivitaData.manifoldCovDerivAlong_model,
    ConnectionVariation.covDerivAlong_def, Fin.sum_univ_two, Function.update,
    add_assoc] using hh




theorem covariant_metric_eq_error {g : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (h : RiemannianMetric 3 E) :
    D.covariantTensorDerivative (fun x v => h.inner x (v 0) (v 1)) =
      D.covariantTensorDerivative (metricError g h) := by
  unfold metricError
  rw [D.covariantTensorDerivative_sub
    (isSmoothCovariantTensor_metric h) (isSmoothCovariantTensor_metric g)]
  funext x v
  have hz := D.covariantTensorDerivative_metric_eq_zero x (v 0) (v 1) (v 2)
  have hv : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
  rw [hv, hz, sub_zero]




theorem inner_connectionDifference {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x u v w : E) :
    2 * h.inner x (connectionDifference g h x u v) w =
      D.covariantTensorDerivative (metricError g h) x ![u, v, w] +
      D.covariantTensorDerivative (metricError g h) x ![v, w, u] -
      D.covariantTensorDerivative (metricError g h) x ![w, u, v] := by
  have hB : ContDiff ℝ ∞ h.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr h.contDiffAt_euclideanCoefficients
  have h1 := fderiv_bilinear_eq_covariant D hB x u v w
  have h2 := fderiv_bilinear_eq_covariant D hB x v w u
  have h3 := fderiv_bilinear_eq_covariant D hB x w u v
  simp only [RiemannianMetric.euclideanCoefficients] at h1 h2 h3
  erw [covariant_metric_eq_error D h] at h1 h2 h3
  have hk := D'.inner_connection_const x u v w
  rw [D'.connection_const_eq_inverse] at hk
  change 2 * h.inner x (christoffelBilinear h.euclideanCoefficients x u v) w = _ at hk
  erw [h1, h2, h3] at hk
  have hs (a b : E) := christoffelBilinear_symm
    ((g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp))
    (Filter.Eventually.of_forall fun y a b => g.symm y a b) a b
  erw [hs v w, hs w u, h.symm x v, h.symm x
    (christoffelBilinear g.euclideanCoefficients x w v) u,
    h.symm x w (christoffelBilinear g.euclideanCoefficients x v u), hs v u] at hk
  have hcancel : 2 * h.inner x (christoffelBilinear h.euclideanCoefficients x u v) w =
      D.covariantTensorDerivative (metricError g h) x ![u, v, w] +
      D.covariantTensorDerivative (metricError g h) x ![v, w, u] -
      D.covariantTensorDerivative (metricError g h) x ![w, u, v] +
      2 * h.inner x (christoffelBilinear g.euclideanCoefficients x u v) w := by
    convert hk using 1
    ring!
  simp only [connectionDifference, sub_apply, map_sub]
  linarith! only [hcancel]



theorem connectionDifference_symm (g h : RiemannianMetric 3 E) (x u v : E) :
    connectionDifference g h x u v = connectionDifference g h x v u := by
  have hs (k : RiemannianMetric 3 E) := christoffelBilinear_symm
    ((k.contDiffAt_euclideanCoefficients x).differentiableAt (by simp))
    (Filter.Eventually.of_forall fun y a b => k.symm y a b) u v
  simp only [connectionDifference, sub_apply, hs]

end PoincareConjecture.M44
