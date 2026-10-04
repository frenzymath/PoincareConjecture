import PoincareLib.Geometry.Riemannian.Comparison.Volume.Jacobi.CurvatureSymmetry
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Radial curvature in isometric frames

Conjugating the retained radial curvature by an isometric frame preserves
symmetry and its Ricci trace. The transported radial vector remains in its
kernel. These are the geometric inputs to the matrix Riccati comparison.

Reference: Morgan--Tian, Theorem 1.34, p. 19.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareMT.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The retained radial curvature conjugated into a fixed Euclidean frame. -/
def radialCurvatureInFrame (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (P.symm.toLinearEquiv.conj (D.radialCurvature x v))

@[simp] theorem radialCurvatureInFrame_apply (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) (u : EuclideanSpace ℝ (Fin n)) :
    D.radialCurvatureInFrame x P v u = P.symm (D.curvature x (P u) v v) := rfl

/-- The radial vector remains in the kernel after transport to a frame. -/
@[simp] theorem radialCurvatureInFrame_radial (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) :
    D.radialCurvatureInFrame x P v (P.symm v) = 0 := by
  simp only [radialCurvatureInFrame_apply, P.apply_symm_apply]
  change P.symm (D.radialCurvature x v v) = 0
  rw [D.radialCurvature_self, map_zero]

/-- Isometric frames give a symmetric Euclidean radial-curvature operator. -/
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

/-- Nonnegative sectional curvature makes the actual radial curvature
nonnegative after transport to an isometric frame. -/
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

/-- The frame coefficient has exactly the retained Ricci trace. -/
theorem trace_radialCurvatureInFrame (D : LeviCivitaData g) (x : M)
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (v : TangentSpace (𝓡 n) x) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.radialCurvatureInFrame x P v).toLinearMap = D.ricci x v v := by
  change LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
    (P.symm.toLinearEquiv.conj (D.radialCurvature x v)) = _
  rw [LinearMap.trace_conj', D.trace_radialCurvature]

end PoincareMT.LeviCivitaData
