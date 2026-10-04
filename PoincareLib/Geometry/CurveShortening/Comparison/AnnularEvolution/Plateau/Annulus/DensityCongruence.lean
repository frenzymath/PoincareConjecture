import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Rectangle.MeasurableIntegration
import PoincareLib.Geometry.RicciFlow.Area.MinimalSphere.EnergyDensityCoordinates
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.PiecewiseArea

/-!
# Rectangle agreement determines annular densities

Maps agreeing on the fundamental rectangle have the same germs in its
interior. Its boundary is null, so their actual area and energy densities
agree almost everywhere. This permits a compactly supported raw variation
to be admitted using its periodic extension.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- Rectangle agreement gives almost-everywhere equality of actual energy densities. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
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

/-- Rectangle agreement gives almost-everywhere equality of actual area densities. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
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

end PoincareMT
