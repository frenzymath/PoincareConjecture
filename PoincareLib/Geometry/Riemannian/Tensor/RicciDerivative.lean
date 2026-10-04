import PoincareLib.Geometry.Riemannian.Curvature.Calculus
import PoincareLib.Geometry.Riemannian.Tensor.Symmetry

/-!
# Symmetry of the covariant Ricci derivative

The raw covariant derivative preserves symmetry of the two Ricci inputs.
This supplies the geometric last-slot symmetry used by the Hamilton tensor.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Symmetry in the Ricci inputs is preserved by the actual covariant derivative. -/
lemma covariantTensorDerivative_ricciEvaluation_symm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative D.ricciEvaluation x ![u, v, w] =
      D.covariantTensorDerivative D.ricciEvaluation x ![u, w, v] := by
  have hsymm (y : M) (a b : TangentSpace (𝓡 n) y) :
      D.ricci y a b = D.ricci y b a :=
    (hD.2.2.2.1 y a b a b).2.2.2
  simp only [covariantTensorDerivative, ricciEvaluation, Fin.sum_univ_two]
  simp [hsymm, add_comm]

/-- The rough Laplacian of the Ricci tensor is symmetric in its tensor inputs. -/
lemma tensorLaplacian_ricciEvaluation_symm
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.ricciEvaluation x ![u, v] =
      D.tensorLaplacian D.ricciEvaluation x ![v, u] := by
  unfold tensorLaplacian
  apply Finset.sum_congr rfl
  intro i _
  simpa only [iteratedCovariantTensorDerivative, Matrix.Fin.cons_vecCons] using
    D.covariantTensorDerivative_symm_last_three (D.covariantTensorDerivative D.ricciEvaluation)
      (D.covariantTensorDerivative_ricciEvaluation_symm hD) x
      (g.orthonormalBasis x i) (g.orthonormalBasis x i) u v

end PoincareMT.LeviCivitaData
