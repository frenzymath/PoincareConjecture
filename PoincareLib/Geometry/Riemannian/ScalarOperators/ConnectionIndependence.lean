import PoincareLib.Geometry.Riemannian.ScalarOperators.Uniqueness
import PoincareLib.Geometry.RicciFlow.Local.Connection.CurvatureIndependence

/-!
# Supporting identities for scalar operators

Connection independence of the Hessian needs only pointwise uniqueness on
a differentiable section. Ricci norm independence uses the previously reviewed
relative Ricci identity. Nonnegativity is a finite sum-of-squares argument.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The field Hessian is independent of the connection on a differentiable second field. -/
theorem hessianOnFields_eq (D D' : LeviCivitaData g) (f : M → ℝ)
    (X Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    D.hessianOnFields f X Y x = D'.hessianOnFields f X Y x := by
  unfold hessianOnFields
  rw [D.connection_eq_at D' Y hY]

/-- The Ricci squared norm is independent of the compatible connection choice. -/
theorem ricciNormSq_eq (D D' : LeviCivitaData g) (x : M) :
    D.ricciNormSq x = D'.ricciNormSq x := by
  simp only [ricciNormSq, D.ricci_eq D']

/-- The Ricci squared norm is nonnegative, including in dimension zero. -/
theorem ricciNormSq_nonneg (D : LeviCivitaData g) (x : M) : 0 ≤ D.ricciNormSq x := by
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

end PoincareMT.LeviCivitaData
