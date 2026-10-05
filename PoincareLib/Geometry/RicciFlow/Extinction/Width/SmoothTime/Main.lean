import PoincareLib.Geometry.RicciFlow.Extinction.Width.SmoothTime.ForwardBound
import PoincareLib.Geometry.RicciFlow.Extinction.Width.SmoothTime.Continuity.Main

/-!
# Smooth-time width estimates

Morgan--Tian Proposition 18.18, pp. 431--432, on an ordinary slab.
The M58, M61, M64, and M65 predecessor services are explicit hypotheses.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology
universe u
namespace PoincareMT

/-- The frozen M66 statement, proved relative to its numbered predecessors. -/
theorem m66_smooth_time_theory
    (hM61 : M61RawWidthCore.{u})
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    {hM64 : M64ComparisonTheory.{u}}
    (hM65 : M65DeformationTheory hM61 hM64) :
    M66SmoothTimeTheory hM61 hM58 hM65 := by
  intro M _ _ _ a b P C
  refine ⟨{
    width_nonnegative := ?_
    forward_difference_bound := m66_forward_difference_bound hM61 hM58 hM65 P C
    continuous_at := m66Width_continuousAt hM61 P }⟩
  intro t
  exact (m66PredecessorsFromServices hM61 hM58 hM65 P C).width t |>.nonnegative

end PoincareMT
