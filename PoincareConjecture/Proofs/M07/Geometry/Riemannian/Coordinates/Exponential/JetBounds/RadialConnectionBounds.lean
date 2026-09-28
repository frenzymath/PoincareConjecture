import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialConnection
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Operator

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem tangentNorm_zero_eq_norm_of_normalized
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (v : EuclideanSpace ℝ (Fin n)) :
    g.tangentNorm 0 v = ‖v‖ := by
  unfold RiemannianMetric.tangentNorm
  rw [h0, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]

theorem norm_inverse_radial_transport
    (D : LeviCivitaData g)
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x v : EuclideanSpace ℝ (Fin n)) :
    ‖(T x).inverse v‖ = g.tangentNorm x v := by
  rw [← tangentNorm_zero_eq_norm_of_normalized h0]
  have h := tangentNorm_radial_field D x ((T x).inverse v)
  rw [← hTv, (hTi x).self_apply_inverse] at h
  exact h.symm

theorem tangentNorm_covariantDerivative_radial_field_le
    (D : LeviCivitaData g)
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (x v w : EuclideanSpace ℝ (Fin n)) {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (t • x) ≤ K)
    (hmetric : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : EuclideanSpace ℝ (Fin n),
      g.tangentNorm (t • x) u ≤ A * ‖u‖) :
    g.tangentNorm x
      (covariantDerivative (christoffelBilinear g.euclideanCoefficients)
        (field (christoffelBilinear g.euclideanCoefficients) v) x w) ≤
      K * A ^ 2 * ‖x‖ * ‖w‖ * ‖v‖ := by
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  obtain ⟨T, hT, hT0, hTv, hTi, hint⟩ := exists_radial_transport_connection_integral hΓ
  rw [← norm_inverse_radial_transport D h0 hTi hTv, hint]
  have hbound (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
      ‖(T (t • x)).inverse
        (christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x)))‖ ≤
        K * A ^ 2 * ‖x‖ * ‖w‖ * ‖v‖ := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ⟨ht.1.le, ht.2⟩
    rw [norm_inverse_radial_transport D h0 hTi hTv]
    have hR : christoffelCurvature Γ (t • x) x (t • w) (field Γ v (t • x)) =
        D.curvature (t • x) x (t • w) (field Γ v (t • x)) := by
      rw [← coordinateCurvature_eq_christoffelCurvature
        ((hΓ.differentiable (by simp)).differentiableAt), coordinateCurvature_eq_retained D]
    rw [hR]
    have hv : g.tangentNorm (t • x) (field Γ v (t • x)) = ‖v‖ :=
      (tangentNorm_radial_field D (t • x) v).trans
        (tangentNorm_zero_eq_norm_of_normalized h0 v)
    have hw : g.tangentNorm (t • x) (t • w) ≤ A * ‖w‖ := by
      apply (hmetric t ht' _).trans
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (norm_nonneg w) ht'.2) hA
    calc
      g.tangentNorm (t • x) (D.curvature (t • x) x (t • w) (field Γ v (t • x))) ≤
          D.curvatureTensorNorm (t • x) * g.tangentNorm (t • x) x *
            g.tangentNorm (t • x) (t • w) * ‖v‖ := by
        simpa only [hv] using D.tangentNorm_curvature_le (t • x) x (t • w) (field Γ v (t • x))
      _ ≤ K * (A * ‖x‖) * (A * ‖w‖) * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        exact mul_le_mul
          (mul_le_mul (hcurv t ht') (hmetric t ht' x) (Real.sqrt_nonneg _) hK)
          hw (Real.sqrt_nonneg _) (by positivity)
      _ = K * A ^ 2 * ‖x‖ * ‖w‖ * ‖v‖ := by ring
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

end PoincareConjecture.CoordinateExponential
