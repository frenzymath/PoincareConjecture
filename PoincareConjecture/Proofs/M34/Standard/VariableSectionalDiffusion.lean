import PoincareConjecture.Proofs.M34.Standard.ParallelTensorProduct
import PoincareConjecture.Proofs.M04.SectionalMinimumDiffusion











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

open M04

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}




theorem curvature_tensorLaplacian_ge_variable_sectional_barrier
    (D : LeviCivitaData g) {h : M → ℝ} (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hmin : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      h y * metricGram g y a b ≤ D.curvatureTensor y a b a b)
    (u v : TangentSpace (𝓡 n) x)
    (hnull : D.curvatureTensor x u v u v = h x * metricGram g x u v) :
    D.laplacian h x * metricGram g x u v ≤
      D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] := by
  let G := metricGramEvaluation g
  have hG : IsSmoothCovariantTensor G := isSmoothCovariantTensor_metricGramEvaluation g
  have hR : IsSmoothCovariantTensor D.riemannEvaluation :=
    isSmoothCovariantTensor_riemannEvaluation D
  let S : CovariantTensorEvaluation n M 4 := fun y w => D.riemannEvaluation y w - h y * G y w
  have hS : IsSmoothCovariantTensor S := hR.sub_tensor (hG.mul_smoothScalar hh)
  have hpair (a b c d : TangentSpace (𝓡 n) x) :
      S x ![a, b, c, d] = S x ![c, d, a, b] := by
    change D.curvatureTensor x a b c d - h x *
        (g.inner x a c * g.inner x b d - g.inner x a d * g.inner x b c) =
      D.curvatureTensor x c d a b - h x *
        (g.inner x c a * g.inner x d b - g.inner x c b * g.inner x d a)
    rw [curvatureTensor_pair_exchange D x a b c d,
      g.symm x c a, g.symm x d b, g.symm x c b, g.symm x d a]
    ring
  have hgram (y : M) (a b : TangentSpace (𝓡 n) y) :
      G y ![a, b, a, b] = metricGram g y a b := by
    change g.inner y a a * g.inner y b b - g.inner y a b * g.inner y b a = _
    rw [g.symm y b a]
    simp only [metricGram, pow_two]
  have hdiag (y : M) (a b : TangentSpace (𝓡 n) y) :
      S y ![a, b, a, b] = D.curvatureTensor y a b a b - h y * metricGram g y a b := by
    change D.curvatureTensor y a b a b - h y * G y ![a, b, a, b] = _
    rw [hgram]
  have hpos := tensorLaplacian_nonneg_at_sectional_null D hS hU hx hpair
    (fun y hy a b => by rw [hdiag]; exact sub_nonneg.mpr (hmin y hy a b)) u v
    (by rw [hdiag]; exact sub_eq_zero.mpr hnull)
  have hdiff : D.tensorLaplacian S x ![u, v, u, v] =
      D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] -
        D.laplacian h x * metricGram g x u v := by
    rw [show S = (fun y w => D.riemannEvaluation y w - h y * G y w) from rfl,
      D.tensorLaplacian_sub_tensor hR (hG.mul_smoothScalar hh),
      D.tensorLaplacian_smoothScalar_mul_parallel hG
        (covariantTensorDerivative_metricGramEvaluation D) hh, hgram]
  rw [hdiff] at hpos
  exact sub_nonneg.mp hpos

end PoincareConjecture.M34
