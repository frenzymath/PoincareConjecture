import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.AlmostEverywhere.Countability
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Lipschitz.ChartFunctionLipschitz
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.AlmostEverywhere.Rademacher
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Regularity.Lipschitz.SliceLipschitz

/-!
# Every-slice almost-everywhere differentiability of reduced length

Morgan-Tian Corollary 6.67 uses Rademacher separately on each positive
interior time slice. The selected measure here is the actual backward
slice metric, while the local Lipschitz producer uses the terminal metric.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

/-- Nondifferentiability is null for the actual measure at every interior backward time. -/
theorem reducedLength_slice_nondifferentiability_eq_zero
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (p : M)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    calibratedMetricVolume (F.metric (T - τ))
      {q | ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
        (fun x ↦ reducedLength F T p x τ) q} = 0 := by
  obtain ⟨G⟩ := hDifferential.exponential_geometry p
  let : SecondCountableTopology M := secondCountableTopology_of_exponential hL G hτ hmax
  apply calibratedMetricVolume_nondifferentiability_eq_zero (F.metric (T - τ))
  exact locallyLipschitz_in_coordinates (F.metric T)
    (reducedLength_slice_locallyLipschitz hL hDifferential hwindow p hτ hmax)

end PoincareMT.ReducedVolume
