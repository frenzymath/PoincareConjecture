import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Proofs.Ch01.CurvatureConnection









set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem hessianOnFields_eq (D D' : LeviCivitaData g) (f : M → ℝ)
    (X Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    D.hessianOnFields f X Y x = D'.hessianOnFields f X Y x := by
  unfold hessianOnFields
  rw [D.connection_eq_at D' Y hY]


theorem hessian_eq (D D' : LeviCivitaData g) (f : M → ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = D'.hessian f x u v := by
  exact D.hessianOnFields_eq D' f _ _ (FiberBundle.mdifferentiableAt_extend ..)


theorem laplacian_eq (D D' : LeviCivitaData g) (f : M → ℝ) (x : M) :
    D.laplacian f x = D'.laplacian f x := by
  simp only [laplacian, D.hessian_eq D']


theorem ricciNormSq_eq (D D' : LeviCivitaData g) (x : M) :
    D.ricciNormSq x = D'.ricciNormSq x := by
  simp only [ricciNormSq, D.ricci_eq D']


theorem ricciNormSq_nonneg (D : LeviCivitaData g) (x : M) : 0 ≤ D.ricciNormSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

end PoincareConjecture.LeviCivitaData
