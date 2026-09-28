import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialFrameVariation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.MetricCompatibility

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

def radialCurvatureComponent (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
    (fun i => field (christoffelBilinear g.euclideanCoefficients) (v i) x)

private theorem contDiff_metricChristoffel (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    ContDiff ℝ ∞ (christoffelBilinear g.euclideanCoefficients) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients x)
    (g.inner_isInvertible x)

theorem contDiff_radialCurvatureComponent (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (radialCurvatureComponent D m v) := by
  let hC := D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m
  have hS : ContDiff ℝ ∞ (LeviCivitaData.tensorCoordinateSection hC
      (0 : EuclideanSpace ℝ (Fin n))) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq] using
      LeviCivitaData.contDiffAt_tensorCoordinateSection hC
        (0 : EuclideanSpace ℝ (Fin n)) (z := x) (by simp)
  have hV : ContDiff ℝ ∞ (fun x => fun i =>
      field (christoffelBilinear g.euclideanCoefficients) (v i) x) :=
    contDiff_pi.mpr (fun i => contDiff_field (contDiff_metricChristoffel g) (v i))
  have he := (TensorFiber.continuousMultilinear
    (E := EuclideanSpace ℝ (Fin n)) (k := 4 + m)).analyticOnNhd_uncurry_of_multilinear
    (s := Set.univ) |>.contDiff (n := ∞)
  change ContDiff ℝ ∞ (fun x => D.iteratedCovariantTensorDerivative
    D.riemannEvaluation m x
      (fun i => field (christoffelBilinear g.euclideanCoefficients) (v i) x))
  simpa only [Function.comp_def, TensorFiber.continuousMultilinear_apply,
    LeviCivitaData.tensorCoordinateSection_apply,
    LeviCivitaData.tensorCoordinateEvaluation_model] using
    he.comp (hS.prodMk hV)

theorem inner_radial_field (D : LeviCivitaData g) (x v w : EuclideanSpace ℝ (Fin n)) :
    g.inner x
        (field (christoffelBilinear g.euclideanCoefficients) v x)
        (field (christoffelBilinear g.euclideanCoefficients) w x) =
      g.inner 0 v w := by
  have hmetric : g.pullbackCoefficients id = g.euclideanCoefficients := by
    funext y
    ext a b
    simp [RiemannianMetric.pullbackCoefficients, RiemannianMetric.euclideanCoefficients]
    rfl
  have hcompat (z u a b : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => g.euclideanCoefficients y a b) z u =
        g.euclideanCoefficients z (christoffelBilinear g.euclideanCoefficients z u a) b +
        g.euclideanCoefficients z a (christoffelBilinear g.euclideanCoefficients z u b) := by
    have h := D.chartMetric_compatibility (0 : EuclideanSpace ℝ (Fin n))
      (z := z) (by simp) u a b
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, id_eq, hmetric,
      D.coordinateConnectionCoefficient_model] using h
  exact field_metric_eq (contDiff_metricChristoffel g) isOpen_univ
    (fun y _ => ((g.contDiffAt_euclideanCoefficients y).differentiableAt
      (by simp)).differentiableWithinAt)
    (fun z _ => hcompat z) x (fun _ _ => mem_univ _) v w

theorem tangentNorm_radial_field (D : LeviCivitaData g)
    (x v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm x (field (christoffelBilinear g.euclideanCoefficients) v x) =
      g.tangentNorm 0 v := by
  unfold RiemannianMetric.tangentNorm
  rw [inner_radial_field D]

theorem fderiv_radialCurvatureComponent (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x d : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (radialCurvatureComponent D m v) x d =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
        (Fin.cons d (fun i => field (christoffelBilinear g.euclideanCoefficients) (v i) x)) +
      ∑ i, D.iteratedCovariantTensorDerivative D.riemannEvaluation m x
        (Function.update
          (fun j => field (christoffelBilinear g.euclideanCoefficients) (v j) x) i
          (covariantDerivative (christoffelBilinear g.euclideanCoefficients)
            (field (christoffelBilinear g.euclideanCoefficients) (v i)) x d)) := by
  have h := D.fderiv_iteratedCurvature_pullback_model m
    (q := id) (p := x)
    (V := fun i y => field (christoffelBilinear g.euclideanCoefficients) (v i) y)
    differentiableAt_id
    (fun i => ((contDiff_field (contDiff_metricChristoffel g) (v i)).differentiable
      (by simp)).differentiableAt) d
  change fderiv ℝ (fun z =>
      D.iteratedCovariantTensorDerivative D.riemannEvaluation m z
        (fun i => field (christoffelBilinear g.euclideanCoefficients) (v i) z)) x d = _
  convert h using 1 <;>
    simp only [id_eq, fderiv_id, ContinuousLinearMap.id_apply,
      LeviCivitaData.manifoldCovDerivAlong_model, covDerivAlong, covariantDerivative]
  congr 1

theorem fderiv_radialCurvatureComponent_radial (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (radialCurvatureComponent D m v) x x =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation (m + 1) x
        (Fin.cons x (fun i => field (christoffelBilinear g.euclideanCoefficients) (v i) x)) := by
  rw [fderiv_radialCurvatureComponent]
  have hzero (i : Fin (4 + m)) :
      covariantDerivative (christoffelBilinear g.euclideanCoefficients)
        (field (christoffelBilinear g.euclideanCoefficients) (v i)) x x = 0 := by
    simpa only [one_smul] using covariantDerivative_field_radial_all
      (contDiff_metricChristoffel g) (v i) x 1
  simp_rw [hzero]
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m).1 x
  simp only [hA, MultilinearMap.map_update_zero, Finset.sum_const_zero, add_zero]

theorem abs_radialCurvatureComponent_le (D : LeviCivitaData g) (m : ℕ)
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    |radialCurvatureComponent D m v x| ≤
      D.curvatureDerivativeNorm m x *
        ∏ i, g.tangentNorm x
          (field (christoffelBilinear g.euclideanCoefficients) (v i) x) := by
  obtain ⟨A, hA⟩ := (D.iteratedCovariantTensorDerivative_isSmooth
    D.riemannEvaluation_isSmooth_model m).1 x
  exact abs_tensor_evaluation_le_tensorNorm g _ x A hA _

theorem abs_radialCurvatureComponent_le_of_curvatureDerivativeNorm_le
    (D : LeviCivitaData g) (m : ℕ) {C : ℝ}
    (v : Fin (4 + m) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (hC : D.curvatureDerivativeNorm m x ≤ C) :
    |radialCurvatureComponent D m v x| ≤ C * ∏ i, g.tangentNorm 0 (v i) := by
  have h := abs_radialCurvatureComponent_le D m v x
  simp_rw [tangentNorm_radial_field D] at h
  exact h.trans (mul_le_mul_of_nonneg_right hC
    (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _))

end PoincareConjecture.CoordinateExponential
