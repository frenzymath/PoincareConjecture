import PoincareConjecture.Proofs.M08.ClosedPhaseAssembly
import PoincareConjecture.Proofs.M08.EulerPathCharts

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]

theorem nonempty_regularizedLGeodesicData {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₂ : τ₂ ≤ τmax) (p : BackwardTimePath F T τ₁ τ₂)
    (hp : IsBackwardLGeodesic F T τ₁ τ₂ p) :
    Nonempty (RegularizedLGeodesicData p) := by
  apply nonempty_regularizedData_of_closed_phase_cover hM04 p
    (squarePath_contMDiffOn_of_euler hM04 hwindow hcurvature hτ₂ p hp)
  intro s hs
  obtain ⟨a, b, x, Pbar, hab, hAa, hbB, hsab, hnear, hsrc, _, _, hphase⟩ :=
    squarePath_local_phase hM04 hwindow hcurvature hτ₂ p hp hs
  exact ⟨a, b, x, Pbar, hab, hsab, Icc_subset_Icc hAa hbB, hnear, hsrc, hphase⟩

end PoincareConjecture.M08
