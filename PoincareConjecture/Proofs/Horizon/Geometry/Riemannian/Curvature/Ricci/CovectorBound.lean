import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Bounds
import Mathlib.Algebra.QuadraticDiscriminant









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  {g : RiemannianMetric n M}


theorem sq_ricci_le_ricci_mul_ricci
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (v w : TangentSpace (𝓡 n) x) :
    (D.ricci x v w) ^ 2 ≤ D.ricci x v v * D.ricci x w w := by
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have hB (a b : TangentSpace (𝓡 n) x) : B a b = D.ricci x a b := by
    simp [B, ricci, LinearMap.sum_apply]
  have hsym : B w v = B v w := by
    simpa only [hB] using (hD.2.2.2.1 x w v v w).2.2.2
  have hq (r : ℝ) :
      0 ≤ B w w * (r * r) + (2 * B v w) * r + B v v := by
    have h := hRic (v + r • w)
    rw [← hB] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hsym] at h
    nlinarith only [h]
  have h := discrim_le_zero hq
  simp only [discrim, hB] at h
  nlinarith only [h]


theorem sum_sq_ricci_le_scalar_mul_ricci
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (hRic : ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (v : TangentSpace (𝓡 n) x) :
    (∑ i, (D.ricci x v (g.orthonormalBasis x i)) ^ 2) ≤
      D.scalarCurvature x * D.ricci x v v := by
  calc
    _ ≤ ∑ i, D.ricci x v v * D.ricci x
        (g.orthonormalBasis x i) (g.orthonormalBasis x i) :=
      Finset.sum_le_sum fun i _ => D.sq_ricci_le_ricci_mul_ricci hD x hRic v _
    _ = _ := by rw [← Finset.mul_sum, mul_comm]; rfl

end PoincareConjecture.LeviCivitaData
