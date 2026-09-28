
import PoincareConjecture.Definitions.Ch01.ScalarOperators
import PoincareConjecture.Proofs.M05.Geometry.Manifold.PartitionOfUnity.Derivative









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


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


lemma laplacian_eq_of_eventuallyEq (D : LeviCivitaData g) {f h : M → ℝ} {x : M}
    (heq : f =ᶠ[𝓝 x] h) : D.laplacian f x = D.laplacian h x := by
  unfold laplacian
  exact Finset.sum_congr rfl fun _ _ => D.hessian_eq_of_eventuallyEq heq _ _

end PoincareConjecture.LeviCivitaData
