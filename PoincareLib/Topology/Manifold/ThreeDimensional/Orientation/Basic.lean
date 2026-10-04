import Mathlib

/-!
# Topological orientation data for three-manifolds

Mathlib provides the local charted-space and homotopy interfaces used here but
does not provide a global orientability class for manifolds.  The witness below
therefore records a sign for every atlas chart and requires the signed Jacobian
of every overlapping chart transition to be positive.  It is a concrete atlas
condition, rather than a pointwise orientation of the tangent fibers.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

/-- A global orientation witness for the chosen smooth three-manifold atlas. -/
structure OrientationCompatibleAtlas (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] where
  /-- The locally constant orientation sign on each chart source. -/
  chartSign :
    ∀ e : {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)) //
      e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M}, e.1.source → Bool
  /-- Signs do not change inside a connected chart-source neighborhood. -/
  chartSign_locallyConstant :
    ∀ e, IsLocallyConstant (chartSign e)
  /-- Signed transition Jacobians are positive on every chart overlap. -/
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

end PoincareMT
