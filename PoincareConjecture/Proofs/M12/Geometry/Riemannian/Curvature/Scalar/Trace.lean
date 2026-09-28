import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Contraction







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureTensor_diagonal_pair_swap (D : LeviCivitaData g) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x v w v w = D.curvatureTensor x w v w v := by
  rw [D.curvatureTensor_swap_first x v w v w,
    D.curvatureTensor_swap_last x w v v w, neg_neg]


theorem scalarCurvature_eq_sum_orthonormalBasis (D : LeviCivitaData g) (x : M)
    {ι : Type*} [Fintype ι]
    (b : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace (𝓡 n) x)) :
    D.scalarCurvature x = ∑ i, ∑ j,
      D.curvatureTensor x (b i) (b j) (b i) (b j) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let c := g.orthonormalBasis x
  change (∑ i, ∑ j, D.curvatureTensor x (c i) (c j) (c i) (c j)) = _
  calc
    _ = ∑ j, ∑ i, D.curvatureTensor x (c i) (c j) (c i) (c j) :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, D.curvatureTensor x (b i) (c j) (b i) (c j) := by
      apply Finset.sum_congr rfl
      intro j _
      exact bilinear_sum_orthonormalBasis_eq
        (D.curvatureTensor_bilinear_first_third x (c j) (c j)) c b
    _ = ∑ i, ∑ j, D.curvatureTensor x (b i) (c j) (b i) (c j) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [curvatureTensor_diagonal_pair_swap D x (b i)]
      exact bilinear_sum_orthonormalBasis_eq
        (D.curvatureTensor_bilinear_first_third x (b i) (b i)) c b

end PoincareConjecture.LeviCivitaData
