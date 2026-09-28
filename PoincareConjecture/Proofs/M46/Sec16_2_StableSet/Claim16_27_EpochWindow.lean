import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_Minimizer

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M46

theorem epochStart_ge_initial (j : ℕ) : 1 / 32 ≤ surgeryEpochStart j := by
  exact div_le_div_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    (by norm_num)

theorem epochStart_succ (j : ℕ) :
    surgeryEpochStart (j + 1) = 2 * surgeryEpochStart j := by
  unfold surgeryEpochStart
  rw [pow_succ]
  ring

theorem prefix_epochStart_eq_twice {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) :
    surgeryEpochStart p.i = 2 * surgeryEpochStart (p.i - 1) := by
  have hi : p.i - 1 + 1 = p.i := Nat.sub_add_cancel p.i_pos
  simpa only [hi] using epochStart_succ (p.i - 1)

theorem prefix_old_time_bounds {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {T : ℝ}
    (hTlo : surgeryEpochStart p.i ≤ T)
    (hThi : T ≤ surgeryEpochStart (p.i + 1)) :
    1 / 32 ≤ T - surgeryEpochStart (p.i - 1) ∧
      2 * surgeryEpochStart (p.i - 1) ≤ T ∧
      T ≤ 4 * surgeryEpochStart (p.i - 1) := by
  rw [prefix_epochStart_eq_twice p] at hTlo
  rw [epochStart_succ, prefix_epochStart_eq_twice p] at hThi
  refine ⟨?_, hTlo, ?_⟩ <;> linarith [epochStart_ge_initial (p.i - 1)]

theorem prefix_low_scalar_time_window {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {T tau : ℝ}
    (hTlo : surgeryEpochStart p.i ≤ T)
    (hThi : T ≤ surgeryEpochStart (p.i + 1))
    (htau : tau ∈ Icc (3 * (T - surgeryEpochStart (p.i - 1)) / 4)
      (7 * (T - surgeryEpochStart (p.i - 1)) / 8)) :
    tau ∈ Icc (max (p.setup.epsilon ^ 2) (T - surgeryEpochStart p.i))
      (T - surgeryEpochStart (p.i - 1) - p.setup.epsilon ^ 2) ∧
      T - tau < surgeryEpochStart p.i := by
  obtain ⟨_, htwo, hfour⟩ := prefix_old_time_bounds p hTlo hThi
  have hwindow := middle_interval_subset_old_window
    (epochStart_ge_initial (p.i - 1)) htwo hfour p.setup.epsilon_pos.le
    (p.setup.epsilon_le.trans (min_le_left _ _)) htau
  rw [← prefix_epochStart_eq_twice p] at hwindow
  refine ⟨hwindow, ?_⟩
  rw [prefix_epochStart_eq_twice p]
  linarith [htau.1, epochStart_ge_initial (p.i - 1)]

theorem prefix_seed_time_slab {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {T tau : ℝ}
    (htau : tau ≤ T - surgeryEpochStart (p.i - 1) - p.setup.epsilon ^ 2)
    (hbefore : T - tau < surgeryEpochStart p.i) :
    Icc (T - tau - p.setup.epsilon ^ 2) (T - tau) ⊆ surgeryEpochEntry p.i := by
  rw [surgeryEpochEntry, if_neg (Nat.ne_of_gt p.i_pos)]
  intro t ht
  exact ⟨by linarith [ht.1], ht.2.trans_lt hbefore⟩

theorem prefix_comparison_time_bounds {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K) {T tau delay radius : ℝ}
    (hT : T ≤ surgeryEpochStart (p.i + 1))
    (htau : tau ∈ Icc (p.setup.epsilon ^ 2)
      (T - surgeryEpochStart (p.i - 1) - p.setup.epsilon ^ 2))
    (hbefore : T - tau < surgeryEpochStart p.i)
    (hdelay : delay ∈ Icc 0 (p.setup.epsilon ^ 2))
    (hradius : 0 < radius) (hradiusle : radius ≤ p.setup.epsilon) :
    0 < tau + delay ∧ tau + delay ≤ surgeryEpochStart (p.i + 1) ∧
      (radius / 2) ^ 2 ≤ tau + delay ∧
      T - (tau + delay) ∈ surgeryEpochEntry p.i := by
  have heps := p.setup.epsilon_pos
  have hepssq : 0 < p.setup.epsilon ^ 2 := sq_pos_of_pos heps
  refine ⟨by linarith [htau.1, hdelay.1], ?_, ?_, ?_⟩
  · linarith [htau.2, hdelay.2, epochStart_ge_initial (p.i - 1)]
  · nlinarith [htau.1, hdelay.1]
  · apply prefix_seed_time_slab p htau.2 hbefore
    constructor <;> linarith [hdelay.1, hdelay.2]

theorem HalfRadiusHistory.low_scalar_minimizer (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O)
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D)
    (hTlo : surgeryEpochStart p.i ≤ D.time)
    (hThi : D.time ≤ surgeryEpochStart (p.i + 1))
    (confinement : ActionConfinement H.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val)
    (M : MinimizingRegion H.spacetime.geometry.toLGeometry
      D.time (surgeryEpochStart (p.i - 1))
      ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
      confinement) :
    ∃ endpoint : H.spacetime.geometry.toLGeometry.Point,
      ∃ path : M14BackwardPath H.spacetime.geometry.toLGeometry D.time 0
        (D.time - surgeryEpochStart (p.i - 1))
        ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
        endpoint,
        M14IsMinimizing path ∧
        M14BackwardLAction H.spacetime.geometry.toLGeometry path ≤
          3 * Real.sqrt (D.time - surgeryEpochStart (p.i - 1)) ∧
        ∃ tau : ℝ,
          tau ∈ Icc (max (p.setup.epsilon ^ 2) (D.time - surgeryEpochStart p.i))
            (D.time - surgeryEpochStart (p.i - 1) - p.setup.epsilon ^ 2) ∧
          D.time - tau < surgeryEpochStart p.i ∧
          horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise
            (path.curve tau) < (p.r (Fin.last p.i))⁻¹ ^ 2 := by
  obtain ⟨hS, _, _⟩ := prefix_old_time_bounds p hTlo hThi
  have hstart : surgeryEpochStart (p.i - 1) < D.time := by linarith
  obtain ⟨endpoint, path, hmin, haction, _⟩ := M.short_path hstart
  have hStime : D.time - surgeryEpochStart (p.i - 1) ≤ D.time := by
    linarith [epochStart_ge_initial (p.i - 1)]
  have hwindow :
      Icc (D.time - (D.time - surgeryEpochStart (p.i - 1))) D.time ⊆
        H.spacetime.history.generalized.interval := by
    rw [H.spacetime.history.interval_eq]
    intro t ht
    change 0 ≤ t ∧ t ≤ D.time
    refine ⟨?_, ht.2⟩
    linarith [ht.1, epochStart_ge_initial (p.i - 1)]
  have hscalar := regular_history_path_scalar_lower P old H.spacetime path
    D.time_mem hStime hwindow
  obtain ⟨tau, htau, hlow⟩ := low_scalar_point_of_action path (sq_nonneg _)
    (prefix_low_scalar_action_margin p hS) hscalar haction
  obtain ⟨htauwindow, htaubefore⟩ := prefix_low_scalar_time_window p hTlo hThi htau
  exact ⟨endpoint, path, hmin, haction, tau, htauwindow, htaubefore, hlow⟩

end PoincareConjecture.Proofs.M46
