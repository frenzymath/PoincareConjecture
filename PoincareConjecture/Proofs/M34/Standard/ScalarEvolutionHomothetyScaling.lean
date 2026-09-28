import PoincareConjecture.Proofs.M13.ConnectionScale
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem scaleLeviCivitaData_gradient (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    (u : M → ℝ) (x : M) :
    (scaleLeviCivitaData D Q hQ).gradient u x = Q⁻¹ • D.gradient u x := by
  apply (g.inner_isInvertible x).injective
  ext v
  have h := (scaleLeviCivitaData D Q hQ).inner_gradient u x v
  change Q * g.inner x ((scaleLeviCivitaData D Q hQ).gradient u x) v =
    mvfderiv (𝓡 n) u x v at h
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient]
  field_simp [hQ.ne'] at h ⊢
  nlinarith



theorem scaleLeviCivitaData_laplacian (D : LeviCivitaData g) {Q : ℝ} (hQ : 0 < Q)
    {u : M → ℝ} {x : M} (hu : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ u x) :
    (scaleLeviCivitaData D Q hQ).laplacian u x = D.laplacian u x / Q := by
  have hgrad : (scaleLeviCivitaData D Q hQ).gradient u = Q⁻¹ • D.gradient u := by
    funext y
    exact scaleLeviCivitaData_gradient D hQ u y
  rw [(scaleLeviCivitaData D Q hQ).laplacian_eq_trace_connection_gradient hu,
    D.laplacian_eq_trace_connection_gradient hu, hgrad]
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
    (D.connection (Q⁻¹ • D.gradient u) x).toLinearMap = _
  rw [D.connection.isCovariantDerivativeOn.smul_const Q⁻¹
    ((D.contMDiffAt_gradient hu).mdifferentiableAt (by simp))]
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x)
    (Q⁻¹ • (D.connection (D.gradient u) x).toLinearMap) = _
  simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]

end PoincareConjecture.M13
