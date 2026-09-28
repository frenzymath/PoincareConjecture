import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.ForwardBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.SmoothTime.Continuity.Main








set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology
universe u
namespace PoincareConjecture


theorem horizon_m66_smooth_time_theory
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

end PoincareConjecture
