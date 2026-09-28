import PoincareConjecture.Definitions.Ch12.StandardCap
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv









set_option autoImplicit false

open scoped Manifold ContDiff

namespace PoincareConjecture.M36

theorem standardRotation_eq_linear (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    standardRotation A = Matrix.toEuclideanLin A.1 := rfl

theorem standardRotation_contDiff (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ContDiff ℝ ∞ (standardRotation A) :=
  (Matrix.toEuclideanLin A.1).toContinuousLinearMap.contDiff

theorem standardRotation_contMDiff (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (standardRotation A) :=
  (standardRotation_contDiff A).contMDiff

theorem standardRotation_mfderiv (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : StandardCapSpace) :
    mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x =
      (Matrix.toEuclideanLin A.1).toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv, standardRotation_eq_linear]
  exact (Matrix.toEuclideanLin A.1).toContinuousLinearMap.hasFDerivAt.fderiv

theorem standardInitialMetric_rotation_inner (g₀ : StandardInitialMetric)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x v w : StandardCapSpace) :
    g₀.metric.inner (Matrix.toEuclideanLin A.1 x)
      (Matrix.toEuclideanLin A.1 v) (Matrix.toEuclideanLin A.1 w) =
        g₀.metric.inner x v w := by
  have h := g₀.rotation_invariant A x v w
  simp only [standardRotation_mfderiv] at h
  exact h

end PoincareConjecture.M36
