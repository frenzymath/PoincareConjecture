import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.EuclideanConstruction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Coordinates










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture

namespace RiemannianMetric


noncomputable def euclideanMetric (n : ℕ) :
    RiemannianMetric n (EuclideanSpace ℝ (Fin n)) :=
  { riemannianMetricVectorSpace (EuclideanSpace ℝ (Fin n)) with
    contMDiff := (riemannianMetricVectorSpace
      (EuclideanSpace ℝ (Fin n))).contMDiff.of_le le_top }

@[simp] lemma euclideanMetric_inner {n : ℕ} (x v w : EuclideanSpace ℝ (Fin n)) :
    (euclideanMetric n).inner x v w = inner ℝ v w := rfl

@[simp] lemma euclideanMetric_tangentNorm {n : ℕ} (x v : EuclideanSpace ℝ (Fin n)) :
    (euclideanMetric n).tangentNorm x v = ‖v‖ := by
  simp only [tangentNorm, euclideanMetric_inner, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg v)]

@[simp] lemma euclideanMetric_christoffel {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    CoordinateExponential.christoffelBilinear (euclideanMetric n).euclideanCoefficients x =
      0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change (innerSL ℝ).inverse (metricKoszulCovector
    (fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ) x) v w) = 0
  simp [metricKoszulCovector]

end RiemannianMetric

namespace LeviCivitaData

variable {n : ℕ} (D : LeviCivitaData (RiemannianMetric.euclideanMetric n))



lemma hessian_euclideanMetric
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) (v w : EuclideanSpace ℝ (Fin n)) :
    D.hessian f x v w = fderiv ℝ (fderiv ℝ f) x v w := by
  rw [D.hessian_eq_fderiv_sub_christoffel hf,
    RiemannianMetric.euclideanMetric_christoffel]
  simp



lemma laplacian_euclideanMetric
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) :
    D.laplacian f x = ∑ i, fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hfm : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x := contMDiffAt_iff_contDiffAt.mpr hf
  rw [D.laplacian_eq_sum_basis_connection_gradient hfm
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [← D.hessian_euclideanMetric hf, D.hessian_eq_inner_connection_gradient hfm]
  change ((EuclideanSpace.basisFun (Fin n) ℝ).repr
    (D.connection (D.gradient f) x (EuclideanSpace.basisFun (Fin n) ℝ i))) i = _
  rw [RiemannianMetric.euclideanMetric_inner, EuclideanSpace.inner_basisFun_real]
  rfl

end LeviCivitaData
end PoincareConjecture
