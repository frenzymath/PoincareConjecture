import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Gradient


set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {n : ℕ} {M : Type*}


noncomputable def conjugateHeatDensity (n : ℕ) (f : M × ℝ → ℝ)
    (t : ℝ) (x : M) : ℝ :=
  Real.rpow (-t) (-(n : ℝ) / 2) * Real.exp (-f (x, t))

namespace RicciFlow

variable [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {J : Set ℝ}

noncomputable def conjugateHeatResidual (F : RicciFlow n M J)
    (u : M × ℝ → ℝ) (t : ℝ) (x : M) : ℝ :=
  deriv (fun s ↦ u (x, s)) t +
    (F.connection t).laplacian (fun y ↦ u (y, t)) x -
    (F.connection t).scalarCurvature x * u (x, t)

noncomputable def potentialResidual (F : RicciFlow n M J)
    (f : M × ℝ → ℝ) (t : ℝ) (x : M) : ℝ :=
  deriv (fun s ↦ f (x, s)) t + (F.connection t).laplacian (fun y ↦ f (y, t)) x -
    (F.metric t).inner x ((F.connection t).gradient (fun y ↦ f (y, t)) x)
      ((F.connection t).gradient (fun y ↦ f (y, t)) x) +
    (F.connection t).scalarCurvature x - n / (2 * -t)

end RicciFlow

end PoincareConjecture
