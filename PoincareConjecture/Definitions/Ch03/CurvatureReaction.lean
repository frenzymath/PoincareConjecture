import PoincareConjecture.Definitions.Ch01.TensorOperators









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def curvatureB (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) *
    D.curvatureTensor x w (b i) z (b j)


noncomputable def curvatureReaction (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  2 * (D.curvatureB x u v w z - D.curvatureB x u v z w -
    D.curvatureB x u z v w + D.curvatureB x u w v z) -
    ∑ i, (D.ricci x u (b i) * D.curvatureTensor x (b i) v w z +
      D.ricci x v (b i) * D.curvatureTensor x u (b i) w z +
      D.ricci x w (b i) * D.curvatureTensor x u v (b i) z +
      D.ricci x z (b i) * D.curvatureTensor x u v w (b i))


noncomputable def ricciReaction (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) : ℝ :=
  let b := g.orthonormalBasis x
  2 * (∑ i, ∑ j, D.curvatureTensor x u (b i) v (b j) * D.ricci x (b i) (b j)) -
    2 * (∑ i, D.ricci x u (b i) * D.ricci x (b i) v)

end PoincareConjecture.LeviCivitaData
