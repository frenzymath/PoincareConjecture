import PoincareConjecture.Proofs.M51.GlobalRepresentatives
import PoincareConjecture.Statements.M13Rescaling

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F₀ : SurgeryFlowData.{u}} {k : ℕ}
  (Q : CompletedStageChain S N C F₀ k)

theorem global_slices_compact (t : ℝ) (ht : 0 ≤ t) :
    IsCompact (univ : Set (Q.globalSlice t).carrier) := by
  have hflow : Q.representativeFlow t = Q.flow (Q.representativeIndex t) := if_pos ht
  exact Eq.mpr (congrArg
    (fun F : SurgeryFlowData.{u} => IsCompact (univ : Set (F.slice t).carrier)) hflow)
    ((Q.flow (Q.representativeIndex t)).slices_compact t (Q.representative_time t ht))

theorem global_no_two_sided_projective_plane (t : ℝ) (ht : 0 ≤ t) :
    SurgeryNoTwoSidedProjectivePlane (Q.globalSlice t) := by
  simpa only [globalSlice, representativeFlow, if_pos ht] using
    (Q.flow (Q.representativeIndex t)).no_two_sided_projective_plane t
      (Q.representative_time t ht)

theorem global_initial_nonempty : Nonempty (Q.globalSlice 0).carrier :=
  (Q.representativeFlow 0).initial_nonempty

theorem global_initial_normalized (x : (Q.globalSlice 0).carrier) :
    (Q.globalConnection 0).curvatureTensorNorm x ≤ 1 ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        ENNReal.ofReal (euclideanUnitBallLebesgueVolume.toReal * r ^ 3 / 2) ≤
          calibratedMetricVolume (Q.globalMetric 0) ((Q.globalMetric 0).ball x r) :=
  (Q.representativeFlow 0).initial_normalized x

theorem global_pinched (t : ℝ) (ht : 0 ≤ t) :
    SurgeryPinchedAt (Q.globalConnection t) t := by
  have hflow : Q.representativeFlow t = Q.flow (Q.representativeIndex t) := if_pos ht
  exact Eq.mpr (congrArg
    (fun F : SurgeryFlowData.{u} => SurgeryPinchedAt (F.connection t) t) hflow)
    (Q.pinched (Q.representativeIndex t) t (Q.representative_time t ht))

theorem global_maximal_intervals
    (H13 : GeneralizedParabolicRescalingTheory.{u} 3)
    (a b : ℝ) (ha : a ∈ Ici (0 : ℝ))
    (hstart : a = 0 ∨ a ∈ Q.globalSurgeryTimes) (hab : a < b)
    (_hI : Ico a b ⊆ Ici 0) (hfree : Disjoint Q.globalSurgeryTimes (Ioo a b))
    [Nonempty (Q.globalSlice a).carrier]
    (hb : b ∈ Q.globalSurgeryTimes ∨ b ∉ Ici (0 : ℝ))
    (L s : ℝ) (hs : s < b) :
    ∃ t ∈ Ioo (max a s) b, ∃ x : (Q.globalSlice t).carrier,
      L < (Q.globalConnection t).curvatureTensorNorm x := by
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := ha0.trans hab.le
  have hbS : b ∈ Q.globalSurgeryTimes :=
    hb.resolve_right (fun h => h hb0)
  obtain ⟨n, hH⟩ := Q.exists_lt_horizon b
  have hJ : Icc a b ⊆ (Q.flow n).time_domain := by
    intro t ht
    exact Q.mem_time_domain_of_lt_horizon n (ha0.trans ht.1) (ht.2.trans_lt hH)
  have haF : a ∈ (Q.flow n).time_domain := hJ ⟨le_rfl, hab.le⟩
  have hbF : b ∈ (Q.flow n).time_domain := hJ ⟨hab.le, le_rfl⟩
  have hstartF : a = 0 ∨ a ∈ (Q.flow n).surgery_times :=
    hstart.imp_right (Q.global_surgery_iff n a haF).mp
  have hIF : Ico a b ⊆ (Q.flow n).time_domain := fun t ht => hJ ⟨ht.1, ht.2.le⟩
  have hfreeF : Disjoint (Q.flow n).surgery_times (Ioo a b) := by
    apply Set.disjoint_left.mpr
    intro t htS htI
    exact Set.disjoint_left.mp hfree (Q.surgery_mem_global n htS) htI
  let : Nonempty ((Q.flow n).slice a).carrier :=
    Nonempty.map (Q.globalIdentify n a haF).symm inferInstance
  obtain ⟨t, ht, x, hx⟩ := (Q.flow n).maximal_intervals a b haF hstartF hab hIF hfreeF
    (Or.inl ((Q.global_surgery_iff n b hbF).mp hbS)) L s hs
  have htF : t ∈ (Q.flow n).time_domain :=
    hJ ⟨(le_max_left a s).trans ht.1.le, ht.2.le⟩
  have H := H13.metric_homothety _ _ ((Q.flow n).metric t) (Q.globalMetric t)
    (Q.globalIdentify n t htF) 1 (by norm_num) (Q.globalIdentify_homothety n t htF)
  refine ⟨t, ht, Q.globalIdentify n t htF x, ?_⟩
  rw [H.curvature_norm_eq ((Q.flow n).connection t) (Q.globalConnection t), div_one]
  exact hx

theorem global_extinction_permanent (s t : ℝ)
    (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ)) (hst : s ≤ t)
    (hempty : IsEmpty (Q.globalSlice s).carrier) : IsEmpty (Q.globalSlice t).carrier := by
  obtain ⟨n, hH⟩ := Q.exists_lt_horizon t
  have hsF := Q.mem_time_domain_of_lt_horizon n hs (hst.trans_lt hH)
  have htF := Q.mem_time_domain_of_lt_horizon n ht hH
  have hsEmpty : IsEmpty ((Q.flow n).slice s).carrier :=
    ⟨fun x => hempty.false (Q.globalIdentify n s hsF x)⟩
  have htEmpty := (Q.flow n).extinction_permanent s t hsF htF hst hsEmpty
  exact ⟨fun x => htEmpty.false ((Q.globalIdentify n t htF).symm x)⟩

end PoincareConjecture.M51.CompletedStageChain
