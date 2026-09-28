import PoincareConjecture.Proofs.M47.SeedM15Action
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_EpochWindow









set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem seedM15_lowScalarMinimizer (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain}
    {x : (F.slice T).carrier} (H : SeedM15TestHistory T hT hTF x r)
    (hTlo : surgeryEpochStart p.i ≤ T)
    (hThi : T ≤ surgeryEpochStart (p.i + 1))
    (confinement : ActionConfinement H.spacetime.geometry.toLGeometry
      T (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val)
    (M : MinimizingRegion H.spacetime.geometry.toLGeometry
      T (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification T).identification H.center).val
      confinement) :
    ∃ endpoint : H.spacetime.geometry.toLGeometry.Point,
      ∃ path : M14BackwardPath H.spacetime.geometry.toLGeometry T 0
        (T - surgeryEpochStart (p.i - 1))
        ((H.spacetime.geometry.sliceIdentification T).identification H.center).val
        endpoint,
        M14IsMinimizing path ∧
        M14BackwardLAction H.spacetime.geometry.toLGeometry path ≤
          3 * Real.sqrt (T - surgeryEpochStart (p.i - 1)) ∧
        ∃ tau : ℝ,
          tau ∈ Icc (max (p.setup.epsilon ^ 2) (T - surgeryEpochStart p.i))
            (T - surgeryEpochStart (p.i - 1) - p.setup.epsilon ^ 2) ∧
          T - tau ≤ surgeryEpochStart p.i - surgeryEpochStart (p.i - 1) / 4 ∧
          horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise
            (path.curve tau) < (p.r (Fin.last p.i))⁻¹ ^ 2 := by
  obtain ⟨hS, _, hfour⟩ := prefix_old_time_bounds p hTlo hThi
  have hstart : surgeryEpochStart (p.i - 1) < T := by linarith
  obtain ⟨endpoint, path, hmin, haction, _⟩ := M.short_path hstart
  have hwindow :
      Icc (T - (T - surgeryEpochStart (p.i - 1))) T ⊆
        H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro t ht
    exact ⟨by linarith [ht.1, epochStart_ge_initial (p.i - 1)], ht.2⟩
  have hscalar := seedM15_path_scalar_lower P hpinch H.spacetime path hwindow
  obtain ⟨tau, htau, hlow⟩ := low_scalar_point_of_action path (sq_nonneg _)
    (prefix_low_scalar_action_margin p hS) hscalar haction
  obtain ⟨htauwindow, _⟩ := prefix_low_scalar_time_window p hTlo hThi htau
  refine ⟨endpoint, path, hmin, haction, tau, htauwindow, ?_, hlow⟩
  rw [prefix_epochStart_eq_twice p]
  linarith [htau.1]



theorem seedM15_lowPoint_before_recent {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {T tau Delta1 b : ℝ}
    (hmargin : T - tau ≤ surgeryEpochStart p.i - surgeryEpochStart (p.i - 1) / 4)
    (hDelta : Delta1 ≤ surgeryEpochStart (p.i - 1) / 2)
    (hbirth : surgeryEpochStart p.i - Delta1 / 2 < b) :
    T - tau < b := by
  linarith

end PoincareConjecture.M47
