import PoincareLib.Geometry.Riemannian.ScalarOperators
import PoincareLib.Geometry.Riemannian.Connection.Uniqueness

/-!
# Independence of scalar operators from the retained connection choice

The canonical local extensions are smooth at their base point, so uniqueness
of the metric-compatible torsion-free connection identifies the Hessian and
its trace. This allows a constructed heat kernel's connection to be matched
to the connection supplied in the original heat-evolution theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The retained scalar Hessian is independent of the connection choice. -/
theorem hessian_eq (D D' : LeviCivitaData g) (f : M → ℝ) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D.hessian f x u v = D'.hessian f x u v := by
  simp only [hessian, hessianOnFields, FiberBundle.extend_apply_self]
  rw [D.connection_eq_of_mdifferentiableAt D'
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)]

/-- The retained scalar Laplacian is independent of the connection choice. -/
theorem laplacian_eq (D D' : LeviCivitaData g) (f : M → ℝ) (x : M) :
    D.laplacian f x = D'.laplacian f x := by
  simp only [laplacian, D.hessian_eq D']

end PoincareMT.LeviCivitaData
