import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureSymmetry
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


def radialCurvatureInFrame (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (P.symm.toLinearEquiv.conj (D.radialCurvature x v))

@[simp] theorem radialCurvatureInFrame_apply (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) (u : EuclideanSpace ℝ (Fin n)) :
    D.radialCurvatureInFrame x P v u = P.symm (D.curvature x (P u) v v) := rfl


@[simp] theorem radialCurvatureInFrame_radial (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) :
    D.radialCurvatureInFrame x P v (P.symm v) = 0 := by
  simp only [radialCurvatureInFrame_apply, P.apply_symm_apply]
  change P.symm (D.radialCurvature x v v) = 0
  rw [D.radialCurvature_self, map_zero]


theorem isSymmetric_radialCurvatureInFrame (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (hP : ∀ u w, g.inner x (P u) (P w) = inner ℝ u w)
    (v : TangentSpace (𝓡 n) x) :
    (D.radialCurvatureInFrame x P v).toLinearMap.IsSymmetric := by
  intro u w
  change inner ℝ (D.radialCurvatureInFrame x P v u) w =
    inner ℝ u (D.radialCurvatureInFrame x P v w)
  rw [← hP, ← hP]
  simpa only [radialCurvatureInFrame_apply, P.apply_symm_apply, radialCurvature_apply] using
    D.inner_radialCurvature_symm x v (P u) (P w)


theorem trace_radialCurvatureInFrame (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.radialCurvatureInFrame x P v).toLinearMap = D.ricci x v v := by
  change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
    (P.symm.toLinearEquiv.conj (D.radialCurvature x v)) = _
  rw [LinearMap.trace_conj', D.trace_radialCurvature]

end PoincareConjecture.LeviCivitaData
