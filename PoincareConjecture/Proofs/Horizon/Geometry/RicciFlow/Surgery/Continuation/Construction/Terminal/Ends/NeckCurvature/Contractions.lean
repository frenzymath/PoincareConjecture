import PoincareConjecture.Proofs.M34.Standard.ScalarMetricJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Trace












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem horizon_scalarCurvature_eq_inverse_gram (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * D.ricci x (b i) (b j) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let B := ∑ i, D.curvatureTensor_bilinear_first_third x
    (g.orthonormalBasis x i) (g.orthonormalBasis x i)
  have h := bilinear_sum_basis_eq_inverse_gram (E := TangentSpace (𝓡 n) x)
    B b (g.orthonormalBasis x)
  change (∑ i, B (g.orthonormalBasis x i) (g.orthonormalBasis x i)) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j * B (b i) (b j) at h
  simpa only [B, LinearMap.sum_apply, curvatureTensor_bilinear_first_third_apply,
    ricci, scalarCurvature] using h

theorem ricci_eq_coordinate_gram (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x))
    (u v : TangentSpace (𝓡 n) x) :
    D.ricci x u v = ∑ i, ∑ j,
      (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
        D.curvatureTensor x u (b i) v (b j) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have h := bilinear_sum_basis_eq_inverse_gram
    (D.curvatureTensor_bilinear_first_third x u v) b (g.orthonormalBasis x)
  change (∑ i, D.curvatureTensor x (g.orthonormalBasis x i) u
      (g.orthonormalBasis x i) v) =
    ∑ i, ∑ j, (Matrix.of (fun i j => g.inner x (b i) (b j)))⁻¹ i j *
      D.curvatureTensor x (b i) u (b j) v at h
  have hswap (a c : TangentSpace (𝓡 n) x) :
      D.curvatureTensor x a u c v = D.curvatureTensor x u a v c := by
    rw [D.curvatureTensor_swap_first, D.curvatureTensor_swap_last x u a c v, neg_neg]
  simpa only [curvatureTensor_bilinear_first_third_apply, hswap, ricci] using h

theorem scalarCurvature_eq_double_inverse_gram (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j, ∑ k, ∑ l,
      (Matrix.of (fun a c => g.inner x (b a) (b c)))⁻¹ i j *
        (Matrix.of (fun a c => g.inner x (b a) (b c)))⁻¹ k l *
          D.curvatureTensor x (b i) (b k) (b j) (b l) := by
  rw [D.horizon_scalarCurvature_eq_inverse_gram x b]
  simp only [D.ricci_eq_coordinate_gram x b, Finset.mul_sum, mul_assoc]

end PoincareConjecture.LeviCivitaData
