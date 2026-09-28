import Mathlib

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

structure OrientationCompatibleAtlas (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] where

  chartSign :
    ∀ e : {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) //
      e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M}, e.1.source → Bool

  chartSign_locallyConstant :
    ∀ e, IsLocallyConstant (chartSign e)

  transition_positive :
    ∀ (e e' : {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) //
      e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M}) (x : M),
      ∀ (hx : x ∈ e.1.source) (hx' : x ∈ e'.1.source),
      0 < (if chartSign e ⟨x, hx⟩ = chartSign e' ⟨x, hx'⟩
        then (1 : ℝ) else -1) *
        LinearMap.det
          ((mfderiv (𝓡 3) (𝓡 3)
            (fun y : EuclideanSpace ℝ (Fin 3) ↦ e'.1 (e.1.symm y))
            (e.1 x)).toLinearMap)

end PoincareConjecture
