import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Slices
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.CoordinateOperator




set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Elliptic.InteriorEstimates

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei

theorem principal_eq_coordinatePrincipal {z : Spacetime n}
    (hx : z.1 ∈ e.source) (i j : Fin n) :
    principal F e i j z =
      LeviCivitaData.Dirichlet.coordinatePrincipalCoefficients
        (F.metric (-z.2)) e z.1 i j := by
  change principal F e i j z =
    (density F e z * principal F e i j z) / density F e z
  exact (eq_div_iff (density_pos F e he hei hx).ne').2 (mul_comm _ _)

theorem drift_eq_coordinateDrift {z : Spacetime n} (hz : z ∈ domain J e)
    (i : Fin n) :
    drift F e i z =
      LeviCivitaData.Dirichlet.coordinateDriftCoefficients
        (F.metric (-z.2)) e i z.1 := by
  change (density F e z)⁻¹ *
      ∑ j, Canonical.spatialDeriv j (weightedPrincipal F e j i) z =
    (∑ j, partialDeriv j (fun y => weightedPrincipal F e j i (y, z.2)) z.1) /
      density F e z
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (partialDeriv_spatialSlice
    (((contDiffOn_weightedPrincipal F e he hei j i).contDiffAt
      ((isOpen_domain e).mem_nhds hz)).differentiableAt (by simp)) j).symm



theorem laplacian_coordinateTest {φ : Spacetime n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {z : Spacetime n} (hz : z ∈ domain J e) :
    (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1) =
      (∑ i, ∑ j, principal F e i j z *
        Canonical.spatialDeriv i (Canonical.spatialDeriv j φ) z) +
      ∑ i, drift F e i z * Canonical.spatialDeriv i φ z := by
  have hs : ContDiff ℝ ∞ (fun x => φ (x, z.2)) :=
    hφ.comp (contDiff_id.prodMk contDiff_const)
  have hu : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => φ (e.symm y, z.2)) e.target := by
    intro y hy
    have hs' : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun x => φ (x, z.2)) (e.symm y) :=
      contMDiffAt_iff_contDiffAt.mpr hs.contDiffAt
    exact (hs'.comp y (hei.contMDiffAt
      (e.open_target.mem_nhds hy))).contMDiffWithinAt
  have hL := LeviCivitaData.Dirichlet.secondOrderOperator_coordinate_eq_laplacian
    (F.connection (-z.2)) e he hei e.open_target hu hz.1 (e.map_source hz.1)
  have heq : ((fun y => φ (e.symm y, z.2)) ∘ e) =ᶠ[𝓝 z.1]
      (fun x => φ (x, z.2)) := by
    filter_upwards [e.open_source.mem_nhds hz.1] with x hx
    simp only [Function.comp_apply, e.left_inv hx]
  rw [← hL, secondOrderOperator_eq_of_eventuallyEq _ _ heq]
  unfold secondOrderOperator
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← principal_eq_coordinatePrincipal F e he hei hz.1 i j,
      partialDeriv_partialDeriv_spatialSlice hφ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← drift_eq_coordinateDrift F e he hei hz i,
      partialDeriv_spatialSlice (hφ.differentiable (by simp) z)]

end PoincareConjecture.RicciFlow.BackwardCoordinates
