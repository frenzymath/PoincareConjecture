import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_CurvatureDifference
import PoincareConjecture.Proofs.M44.Mathlib.BilinearEvaluationDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

open CoordinateExponential

local notation "E" => EuclideanSpace ℝ (Fin 3)




theorem fderiv_metric_evaluation (h : RiemannianMetric 3 E) (x d u v : E) :
    fderiv ℝ (fun y => h.euclideanCoefficients y u v) x d =
      fderiv ℝ h.euclideanCoefficients x d u v := by
  have hh := ((h.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)).hasFDerivAt
  have he := (hh.clm_apply (hasFDerivAt_const u x)).clm_apply (hasFDerivAt_const v x)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, zero_apply, map_zero, add_zero, zero_add] using
      congrArg (fun L => L d) he.fderiv



theorem fderiv_inner_connectionDifference (g h : RiemannianMetric 3 E)
    (x d u v w : E) :
    fderiv ℝ (fun y => h.euclideanCoefficients y (connectionDifference g h y u v) w) x d =
      fderiv ℝ h.euclideanCoefficients x d (connectionDifference g h x u v) w +
      h.inner x (fderiv ℝ (connectionDifference g h) x d u v) w := by
  exact fderiv_bilinear_evaluation_bilinear
    ((h.contDiffAt_euclideanCoefficients x).differentiableAt (by simp))
    ((contDiff_connectionDifference g h).differentiable (by simp) x) d u v w

set_option maxHeartbeats 800000 in




theorem covariant_koszul_error_eq_lowered {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x d u v w : E) :
    D.covariantTensorDerivative
      (koszulPermutation (D.covariantTensorDerivative (metricError g h))) x ![d, u, v, w] =
      2 * h.inner x (covariantConnectionDifference g h x d u v) w +
      2 * D.covariantTensorDerivative (metricError g h) x
        ![d, connectionDifference g h x u v, w] := by
  let A := D.covariantTensorDerivative (metricError g h)
  let Q := koszulPermutation A
  have hA : IsSmoothCovariantTensor A :=
    D.covariantTensorDerivative_isSmooth (metricError_isSmooth g h)
  have hQ : IsSmoothCovariantTensor Q := koszulPermutation_isSmooth hA
  have hQeval (y a b c : E) : Q y ![a, b, c] =
      2 * h.inner y (connectionDifference g h y a b) c := by
    change koszulPermutation A y ![a, b, c] = _
    erw [koszulPermutation_apply]
    exact (inner_connectionDifference D D' y a b c).symm
  have hc := D.fderiv_covariantTensor_pullback_model hQ
    (q := id) (V := fun i (_ : E) => (![u, v, w] : Fin 3 → E) i) (p := x)
    differentiableAt_id (fun i => differentiableAt_const ((![u, v, w] : Fin 3 → E) i)) d
  have hc' : fderiv ℝ (fun y => Q y ![u, v, w]) x d =
      D.covariantTensorDerivative Q x ![d, u, v, w] +
        Q x ![christoffelBilinear g.euclideanCoefficients x d u, v, w] +
        Q x ![u, christoffelBilinear g.euclideanCoefficients x d v, w] +
        Q x ![u, v, christoffelBilinear g.euclideanCoefficients x d w] := by
    have h0 (a : E) : Function.update (![u, v, w] : Fin 3 → E) 0 a = ![a, v, w] := by
      ext i
      fin_cases i <;> rfl
    have h1 (a : E) : Function.update (![u, v, w] : Fin 3 → E) 1 a = ![u, a, w] := by
      ext i
      fin_cases i <;> rfl
    have h2 (a : E) : Function.update (![u, v, w] : Fin 3 → E) 2 a = ![u, v, a] := by
      ext i
      fin_cases i <;> rfl
    simpa! [id_eq, LeviCivitaData.manifoldCovDerivAlong_model,
      ConnectionVariation.covDerivAlong_def, Fin.sum_univ_three, h0, h1, h2,
      add_assoc] using hc
  have hh := (h.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)
  have hC := (contDiff_connectionDifference g h).differentiable (by simp) x
  have hinner := ((hh.clm_apply
    ((hC.clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v))).clm_apply
      (differentiableAt_const w))
  have hder : fderiv ℝ (fun y => Q y ![u, v, w]) x d =
      2 * (fderiv ℝ h.euclideanCoefficients x d (connectionDifference g h x u v) w +
        h.inner x (fderiv ℝ (connectionDifference g h) x d u v) w) := by
    simp_rw [hQeval]
    change fderiv ℝ (fun y => 2 *
      h.euclideanCoefficients y (connectionDifference g h y u v) w) x d = _
    rw [fderiv_const_mul hinner, smul_apply, smul_eq_mul, fderiv_inner_connectionDifference]
  have hm := fderiv_bilinear_eq_covariant D
    (contDiff_iff_contDiffAt.mpr h.contDiffAt_euclideanCoefficients)
    x d (connectionDifference g h x u v) w
  rw [fderiv_metric_evaluation] at hm
  change fderiv ℝ h.euclideanCoefficients x d (connectionDifference g h x u v) w =
    D.covariantTensorDerivative (fun y z => h.inner y (z 0) (z 1)) x
      ![d, connectionDifference g h x u v, w] +
    h.inner x (christoffelBilinear g.euclideanCoefficients x d
      (connectionDifference g h x u v)) w +
    h.inner x (connectionDifference g h x u v)
      (christoffelBilinear g.euclideanCoefficients x d w) at hm
  rw [covariant_metric_eq_error D h] at hm
  rw [hder, hm, hQeval, hQeval, hQeval] at hc'
  change D.covariantTensorDerivative Q x ![d, u, v, w] = _
  simp only [covariantConnectionDifference, map_sub, map_add, sub_apply, add_apply]
  linarith! only [hc']




theorem inner_covariantConnectionDifference {g h : RiemannianMetric 3 E}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x d u v w : E) :
    2 * h.inner x (covariantConnectionDifference g h x d u v) w =
      D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, u, v, w] +
      D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, v, w, u] -
      D.iteratedCovariantTensorDerivative (metricError g h) 2 x ![d, w, u, v] -
      2 * D.covariantTensorDerivative (metricError g h) x
        ![d, connectionDifference g h x u v, w] := by
  have hh := covariant_koszul_error_eq_lowered D D' x d u v w
  rw [covariant_koszulPermutation D
    (D.covariantTensorDerivative_isSmooth (metricError_isSmooth g h))] at hh
  change _ = _ at hh
  dsimp only [LeviCivitaData.iteratedCovariantTensorDerivative]
  linarith only [hh]

end PoincareConjecture.M44
