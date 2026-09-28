import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Equation.SquaredDefect








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem solitonDefectNormSq_expansion (D : LeviCivitaData g)
    (f : M → ℝ) (c : ℝ) (x : M) :
    let b := g.orthonormalBasis x
    D.solitonDefectNormSq f c x = D.ricciNormSq x +
      (∑ i, ∑ j, (D.hessian f x (b i) (b j)) ^ 2) +
      2 * (∑ i, ∑ j, D.ricci x (b i) (b j) * D.hessian f x (b i) (b j)) -
      2 * c * (D.scalarCurvature x + D.laplacian f x) + (n : ℝ) * c ^ 2 := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hmetric (i j) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have he (i j) :
      (D.ricci x (b i) (b j) + D.hessian f x (b i) (b j) -
          c * g.inner x (b i) (b j)) ^ 2 =
        (D.ricci x (b i) (b j)) ^ 2 + (D.hessian f x (b i) (b j)) ^ 2 +
          2 * (D.ricci x (b i) (b j) * D.hessian f x (b i) (b j)) -
          2 * c * (if i = j then D.ricci x (b i) (b j) +
            D.hessian f x (b i) (b j) else 0) +
          (if i = j then c ^ 2 else 0) := by
    rw [hmetric]
    split_ifs <;> ring
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
    finrank_euclideanSpace_fin
  dsimp only [b] at he
  simp only [solitonDefectNormSq, he,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdim]
  simp only [ricciNormSq, scalarCurvature, laplacian,
    Finset.sum_add_distrib]

end PoincareConjecture.LeviCivitaData
