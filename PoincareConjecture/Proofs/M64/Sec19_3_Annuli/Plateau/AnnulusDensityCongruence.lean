import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.EnergyDensityCoordinates
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.PiecewiseArea

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64Annulus_energyDensity_ae_eq_of_eqOn
    (g : RiemannianMetric n M) {f h : LoopPlane → M}
    (heq : EqOn f h m64AnnulusDomain) :
    m60EnergyDensity g f =ᵐ[volume.restrict m64AnnulusDomain]
      m60EnergyDensity g h := by
  rw [m64Annulus_restrict_closed_eq_interior]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  apply m60EnergyDensity_congr_of_eventuallyEq g
  filter_upwards [isOpen_interior.mem_nhds hp] with q hq
  exact heq (interior_subset hq)

theorem m64Annulus_areaDensity_ae_eq_of_eqOn
    (g : RiemannianMetric n M) {f h : LoopPlane → M}
    (heq : EqOn f h m64AnnulusDomain) :
    m60AreaDensity g f =ᵐ[volume.restrict m64AnnulusDomain]
      m60AreaDensity g h := by
  rw [m64Annulus_restrict_closed_eq_interior]
  filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
  apply m60AreaDensity_congr_of_eventuallyEq g
  filter_upwards [isOpen_interior.mem_nhds hp] with q hq
  exact heq (interior_subset hq)

end PoincareConjecture
