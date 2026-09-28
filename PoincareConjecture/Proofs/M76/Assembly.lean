import PoincareConjecture.Definitions.M76SmoothingBridge
import PoincareConjecture.Proofs.M76.Mathlib.AtlasTransport
import PoincareConjecture.Proofs.M76.Smoothing.AtlasConstruction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M76

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

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

theorem smoothingConclusion_of_coordinates {ι : Type*}
    (P : SmoothingBridgeInput (M := M))
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, ContDiffOn ℝ ∞ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) : M76SmoothingConclusion P :=
  (smoothingConclusion_iff_exists_atlas P).mpr
    (exists_smooth_atlas_of_coordinates c hcover hcompat)

theorem smoothingConclusion_of_analytic_coordinates {ι : Type*}
    (P : SmoothingBridgeInput (M := M))
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hcover : ∀ x : M, ∃ i, x ∈ (c i).source)
    (hcompat : ∀ i j, AnalyticOnNhd ℝ ((c i).symm.trans (c j))
      ((c i).symm.trans (c j)).source) : M76SmoothingConclusion P :=
  (smoothingConclusion_iff_exists_atlas P).mpr
    (exists_smooth_atlas_of_analytic_coordinates c hcover hcompat)

end PoincareConjecture.M76
