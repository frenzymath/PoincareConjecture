import PoincareLib.Geometry.RicciFlow.Compactness.Ancient.Window
import PoincareLib.Geometry.RicciFlow.Completeness

/-!
# Completeness of a bounded ancient flow

The complete reference slice and the curvature bound of the actual ancient
flow give completeness at every time by finite-window metric comparison.
Reference: Kleiner--Lott, Appendix E, Corollary E.2, pp. 2848--2849.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- A globally bounded ancient flow with a complete zero slice is complete
throughout its ancient time interval. -/
theorem metricComplete_of_ancient_uniform_curvature_bound
    {n : ℕ} (C : FlowCarrier n) {T K : ℝ} (hT : 0 < T)
    (F : RicciFlow n C.carrier (Iio T)) (p : C.carrier)
    (hcomplete : C.metricComplete (F.metric 0)) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Iio T, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Iio T, C.metricComplete (F.metric t) := by
  intro t ht
  let a := min t 0 - 1
  have ha : a < 0 := by dsimp [a]; linarith [min_le_right t 0]
  have hat : a < t := by dsimp [a]; linarith [min_le_left t 0]
  let B := C.basedWindow F p (fun _ hs => hs.2 : Ioo a T ⊆ Iio T) (ha.trans hT)
  exact B.complete_interior_of_two_time_curvature_bound ⟨ha, hT⟩ hcomplete
    (fun _ _ => ⟨K, hK, fun _ _ s hs x _ => hbound s hs.2 x⟩) t ⟨hat, ht⟩

end PoincareMT.RicciFlow
