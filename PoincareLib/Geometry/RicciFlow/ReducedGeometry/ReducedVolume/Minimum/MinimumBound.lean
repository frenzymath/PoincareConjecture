import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Minimum.MinimumAttainment
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Minimum.MinimumBarrierComparison

/-!
# The sharp reduced-length minimum bound

Morgan-Tian Theorem 7.10 and Claim 7.11, pp. 154-156. Produced compact
sublevels and the initial infimum limit supply the hypotheses of the
upper-barrier comparison, including attainment of the spatial minimum.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

/-- The actual spatial minimum exists and is at most half the dimension. -/
theorem reducedLength_minimum_bound
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (p : M) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    ∃ q : M, (∀ y : M, reducedLength F T p q τ ≤ reducedLength F T p y τ) ∧
      reducedLength F T p q τ ≤ (n : ℝ) / 2 := by
  obtain ⟨G⟩ := hDifferential.exponential_geometry p
  obtain ⟨hcont, hattain⟩ := reducedLength_minimum_data hL G hDifferential hwindow hcurvature
  exact reducedLength_minimum_bound_of_attainment hL G hDifferential (hτ.trans hmax)
    hT hwindow hcurvature hcont hattain hτ hmax

end PoincareMT.ReducedVolume
