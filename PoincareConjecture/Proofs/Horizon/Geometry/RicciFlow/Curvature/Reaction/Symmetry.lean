import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma curvatureB_pair_symm (D : LeviCivitaData g) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    D.curvatureB x a b c d = D.curvatureB x c d a b := by
  unfold curvatureB
  simp only [mul_comm]

lemma curvatureB_swap_pairs (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    D.curvatureB x a b c d = D.curvatureB x b a d c := by
  unfold curvatureB
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(hD.2.2.2.1 x a _ b _).2.1, (hD.2.2.2.1 x c _ d _).2.1]

end PoincareConjecture.LeviCivitaData
