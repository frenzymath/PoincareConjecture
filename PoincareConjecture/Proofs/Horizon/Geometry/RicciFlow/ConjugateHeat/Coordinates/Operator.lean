import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Laplacian
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.ForwardEquation




set_option autoImplicit false

open Set
open scoped Manifold ContDiff
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem laplacian_coordinateTest_forward {φ : Spacetime n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {z : Spacetime n} (hz : z ∈ domain J e) :
    (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1) =
      (∑ i, ∑ j, principal F e i j z *
        Canonical.spatialDeriv j (Canonical.spatialDeriv i φ) z) +
      ∑ i, drift F e i z * Canonical.spatialDeriv i φ z := by
  rw [laplacian_coordinateTest F e he hei hφ hz]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [principal_symm F e he hei hz.1 j i]

theorem forwardCoefficients_adjoint_eq_coordinateLaplacian
    {φ : Spacetime n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {z : Spacetime n} (hz : z ∈ domain J e) :
    (Canonical.forwardCoefficients (principal F e) (drift F e)).adjoint φ z =
      -Canonical.timeDeriv φ z -
        (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1) := by
  rw [Canonical.forwardCoefficients_adjoint (isOpen_domain e)
    (contDiffOn_principal F e he hei) (contDiffOn_drift F e he hei)
    hφ.contDiffOn hz, laplacian_coordinateTest_forward F e he hei hφ hz]
  ring

end PoincareConjecture.RicciFlow.BackwardCoordinates
