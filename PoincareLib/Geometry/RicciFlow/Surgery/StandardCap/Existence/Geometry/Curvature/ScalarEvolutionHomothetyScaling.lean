import PoincareLib.Geometry.Riemannian.Homothety.Connection.Scaling
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Connection.Scaling
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.Riemannian.Homothety.Metric
import PoincareLib.Geometry.Riemannian.ScalarOperators.Divergence

/-!
# Actual scalar operators under constant metric scaling

Metric duality scales the actual gradient, while the retained connection
and its linear trace scale the actual Laplacian. These are the scalar
evolution scaling factors used in Theorem 12.28, pp. 323-324; see
scalar-evolution-homothety.md, section 3.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Positive constant metric scaling divides the actual gradient by
the scale, including totalized scalar differentials (Theorem 12.28). -/
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

/-- The actual Laplacian on a smooth scalar germ is divided by a
positive constant metric scale (Theorem 12.28, pp. 323-324). -/
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

end PoincareMT.M13
