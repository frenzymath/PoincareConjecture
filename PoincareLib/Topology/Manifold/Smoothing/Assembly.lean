import PoincareLib.Topology.Manifold.Poincare.Smoothing.Conclusion
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.AtlasTransport
import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Coordinates.AtlasConstruction

/-!
# Assembling the compatible smoothing bridge

A smooth replacement atlas for the original topology gives exactly the frozen
conclusion, and any model in that conclusion yields such an atlas by pullback.
This is the final composition of Hamilton 1976, Theorem 2(1), p. 69, and
Cairns 1940, Theorem III, p. 797; see M76 derivation 02. Neither of those
existence theorems is assumed or proved in this assembly module.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M76

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

/-- A compatible smooth replacement atlas supplies the frozen bridge on the
original carrier, hence in the required universe. See M76 derivation 02. -/
def smoothingBridgeOfAtlas (P : SmoothingBridgeInput (M := M))
    (a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M)
    (ha : letI := a; IsManifold (𝓡 3) ∞ M) : SmoothingBridgeConclusion P where
  model := M
  model_topology := inferInstance
  model_charted := a
  model_manifold := ha
  model_t2 := inferInstance
  model_second_countable := inferInstance
  model_compact := inferInstance
  model_connected := P.connected
  model_homeomorph := Homeomorph.refl M

/-- The contract is equivalent to finding a smooth atlas for the original
topology; the arbitrary input atlas need not be smooth. See M76 derivation 02. -/
theorem smoothingConclusion_iff_exists_atlas (P : SmoothingBridgeInput (M := M)) :
    M76SmoothingConclusion P ↔
      ∃ a : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
        letI := a; IsManifold (𝓡 3) ∞ M := by
  constructor
  · rintro ⟨S⟩
    let := S.model_topology
    let := S.model_charted
    let := S.model_manifold
    exact ⟨S.model_homeomorph.pullbackChartedSpace,
      S.model_homeomorph.isManifold_pullbackChartedSpace (𝓡 3) ∞⟩
  · rintro ⟨a, ha⟩
    exact ⟨smoothingBridgeOfAtlas P a ha⟩

/-- A smooth coordinate cover assembles to the frozen conclusion, preserving
the original topology and universe. See Cairns p. 806 and M76 derivations 02, 05. -/
theorem smoothingConclusion_of_coordinates {ι : Type*}
    (P : SmoothingBridgeInput (M := M))
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, ContDiffOn ℝ ∞ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) : M76SmoothingConclusion P :=
  (smoothingConclusion_iff_exists_atlas P).mpr
    (exists_smooth_atlas_of_coordinates c hcover hcompat)

/-- Analytic coordinates give the frozen smooth bridge after lowering their
regularity. See Cairns Theorem III, p. 797, and M76 derivations 02, 05. -/
theorem smoothingConclusion_of_analytic_coordinates {ι : Type*}
    (P : SmoothingBridgeInput (M := M))
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, AnalyticOnNhd ℝ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) : M76SmoothingConclusion P :=
  (smoothingConclusion_iff_exists_atlas P).mpr
    (exists_smooth_atlas_of_analytic_coordinates c hcover hcompat)

end PoincareMT.M76
