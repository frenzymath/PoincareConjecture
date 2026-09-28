import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CapBarrierWindow









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M46 Proofs.M12



theorem seedM15_capBarrierWindow
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) (G : FlowBoxRicciGeometry H.generalized)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3) (O : SurgeryObservation F)
    {t T A eta theta c mu : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    (htT : t < T) (hTH : T ≤ O.H) (htheta : 0 < theta)
    (hwindow : Icc 0 T ⊆ H.generalized.interval)
    (hmetric : ∀ (I : Set ℝ) (U : Set (F.slice t).carrier)
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
      (initial : SurgeryCapInitialComparison F t hT i A),
      SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart →
      ∀ hzero : (0 : ℝ) ∈ I, ∀ (s : ℝ) (hs : s ∈ I), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A, ∀ v : StandardCapSpace,
        mu * capComparisonCoefficients e initial.chart 0 hzero x v v ≤
          capComparisonCoefficients e initial.chart s hs x v v)
    (hscalar : ∀ (I : Set ℝ) (U : Set (F.slice t).carrier)
      (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
      (initial : SurgeryCapInitialComparison F t hT i A),
      SurgeryCapFamilyComparison F O.standard_flow A eta e initial.chart →
      ∀ (s : ℝ) (hs : s ∈ I), s ≤ theta →
      ∀ x ∈ F.standard_initial.metric.ball 0 A,
        c / (2 * (1 - s) * (F.parameters.h t) ^ 2) ≤
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (e.forward s hs (initial.chart x)))
    (control : SurgeryCapPersistenceAlternative F O t hT i A eta theta) :
    ∃ Q : CapBarrierWindow G (F.slice t) (F.metric t) ((F.event t hT).caps i).tip
      t T A (F.parameters.h t) c mu theta, Nonempty (CapBarrierOriginData H Q) := by
  have ht0 : 0 ≤ t := F.time_domain_nonnegative (F.surgery_times_subset hT)
  have hh : 0 < F.parameters.h t := F.parameters.h_pos t ht0
  have hsq : 0 < (F.parameters.h t) ^ 2 := sq_pos_of_pos hh
  obtain ⟨top, httop, htopmodel, e, initial, comparison, based, kind⟩ :=
    exists_capPersistence_source_window O i hh (htT.trans_le hTH) htheta control
  have hU : IsOpen ((F.metric t).ball ((F.event t hT).caps i).tip
      (A * F.parameters.h t)) := by
    rw [← comparison.choose_spec.2.2.2.1]
    exact (capInitialPartialDiffeomorph initial).open_target
  let U : TopologicalSpace.Opens (F.slice t).carrier :=
    ⟨(F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t), hU⟩
  let J := capOpenInterval t (min T top) (F.parameters.h t) (lt_min htT httop) hh
  have hwindow' : Ioo t (min T top) ⊆ H.generalized.interval := by
    intro s hs
    exact hwindow ⟨ht0.trans hs.1.le, hs.2.le.trans (min_le_left _ _)⟩
  obtain ⟨hJI, htime, d, forward, metric⟩ :=
    exists_capCylinder_test_window_lift H hU hh httop htT hwindow' e
  have hphysical : (cylinderPhysicalInterval t ((F.parameters.h t)⁻¹ ^ 2)
      d.scale_pos J).domain = Ioo t (min T top) :=
    capOpenInterval_physical t (min T top) (F.parameters.h t) (lt_min htT httop) hh d.scale_pos
  have hzero : (0 : ℝ) ∈ Ico 0 ((top - t) / (F.parameters.h t) ^ 2) :=
    ⟨le_rfl, div_pos (sub_pos.mpr httop) hsq⟩
  have hsTheta (s : ℝ) (hs : s ∈ J.domain) : s ≤ theta := by
    apply (hJI hs).2.le.trans
    exact (div_le_iff₀ hsq).mpr (by linarith)
  refine ⟨{
    top := min T top
    top_gt := lt_min htT httop
    top_le_test := min_le_left _ _
    top_le_model := (min_le_right _ _).trans htopmodel
    source := U
    source_eq := rfl
    interval := J
    cylinder := d
    physical_eq := hphysical
    time_subset := hphysical ▸ hwindow'
    metric_lower := ?_
    scalar_lower := ?_
    top_kind := ?_ }, ?_⟩
  · intro s hs z v
    rw [metric s hs z.val z.property v v]
    exact capCylinder_physicalBirth_lower e initial comparison hzero
      (based hzero) (hJI hs)
      (hmetric _ _ e initial comparison hzero s (hJI hs) (hsTheta s hs)) z.property v
  · intro w
    let s := cylinderClockHomeomorph t ((F.parameters.h t)⁻¹ ^ 2) d.scale_pos J w.1
    have hread := historyCylinder_scalar_pullback H G hM13 e d hJI htime forward
      s.property w.2.property
    change c / (2 * (1 - (w.1.val - t) / (F.parameters.h t) ^ 2) *
      (F.parameters.h t) ^ 2) ≤
        horizontalScalarCurvature G.toLGeometry.leafwise (d.pointMap s.val s.property w.2.val)
    rw [hread]
    have hclock : (w.1.val - t) / (F.parameters.h t) ^ 2 = s.val := by
      change (w.1.val - t) / (F.parameters.h t) ^ 2 =
        parabolicTime ((F.parameters.h t)⁻¹ ^ 2) t w.1.val
      unfold parabolicTime
      simp only [inv_pow, div_eq_mul_inv, mul_comm]
    rw [hclock]
    exact capCylinder_physicalScalar_lower e initial comparison (hJI s.property)
      (hscalar _ _ e initial comparison s.val (hJI s.property) (hsTheta s.val s.property))
        w.2.property
  · by_cases htest : T ≤ top
    · exact Or.inl (min_eq_left htest)
    have hmin : min T top = top := min_eq_right (le_of_not_ge htest)
    rcases kind with hobs | hfull | hdisappears
    · have : T ≤ top := by rw [hobs]; exact hTH
      exact (htest this).elim
    · exact Or.inr (Or.inl (hmin.trans hfull))
    · right
      right
      intro v hv
      apply rawCylinder_closure_excludes_disappearing_top (U := U) (J := J)
        G.realization H.history e d hJI htime forward hdisappears _ v (hv.trans hmin)
      intro s hs
      rw [inv_pow, div_inv_eq_mul]
      have h := (lt_div_iff₀ hsq).mp hs.2
      linarith
  · exact ⟨{
      originalTop := top
      top_le_original := min_le_right _ _
      original := e
      based := based
      interval_eq := rfl
      interval_subset := hJI
      time_mem := htime
      forward := forward }⟩

end PoincareConjecture.M47
