import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureFrame
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureSymmetry
import Mathlib.Analysis.InnerProductSpace.Symmetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem radialCurvatureInFrame_nonneg_of_orthonormal
    (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (hP : ∀ u w, g.inner x (P u) (P w) = inner ℝ u w)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 ≤ D.sectionalCurvature x u v)
    (v : TangentSpace (𝓡 n) x) (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ inner ℝ (D.radialCurvatureInFrame x P v u) u := by
  rw [← hP, radialCurvatureInFrame_apply, P.apply_symm_apply]
  exact D.curvatureTensor_diagonal_nonneg_of_orthonormal x hsec (P u) v

end PoincareConjecture.LeviCivitaData
