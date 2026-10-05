import PoincareLib.Geometry.Riemannian.ScalarOperators
import PoincareLib.Geometry.Manifold.PartitionOfUnity.Derivative

/-!
# Locality of scalar differential operators

The retained Hessian and Laplacian depend only on the germ of their scalar
argument. These identities are shared by compact-test heat equations and
the tensor maximum principle.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The scalar Hessian depends only on the scalar germ. -/
lemma hessian_eq_of_eventuallyEq (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (heq : f =ᶠ[𝓝 x] h) (a b : TangentSpace (𝓡 n) x) :
    D.hessian f x a b = D.hessian h x a b := by
  have hi : (fun y => mvfderiv (𝓡 n) f y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b y)) =ᶠ[𝓝 x]
      (fun y => mvfderiv (𝓡 n) h y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) b y)) := by
    filter_upwards [heq.eventually_nhds] with y hy
    rw [Poincare.mvfderiv_eq_of_eventuallyEq hy]
  simp only [hessian, hessianOnFields, Poincare.mvfderiv_eq_of_eventuallyEq hi,
    Poincare.mvfderiv_eq_of_eventuallyEq heq]

/-- The scalar Laplacian depends only on the scalar germ. -/
lemma laplacian_eq_of_eventuallyEq (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (heq : f =ᶠ[𝓝 x] h) : D.laplacian f x = D.laplacian h x := by
  unfold laplacian
  exact Finset.sum_congr rfl fun _ _ => D.hessian_eq_of_eventuallyEq heq _ _

end PoincareMT.LeviCivitaData
