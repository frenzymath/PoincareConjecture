import PoincareConjecture.Proofs.M33.RegularHistory










set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.SurgeryFlowData

theorem emptyTime_pos (F : SurgeryFlowData.{u}) {a : ℝ}
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier] : 0 < a := by
  have ha0 := F.time_domain_nonnegative ha
  by_contra h
  have haeq : a = 0 := le_antisymm (le_of_not_gt h) ha0
  subst a
  obtain ⟨x⟩ := F.initial_nonempty
  exact isEmptyElim x



theorem surgeryTime_le_empty (F : SurgeryFlowData.{u}) {a T : ℝ}
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier]
    (hT : T ∈ F.surgery_times) : T ≤ a := by
  by_contra h
  have haT : a < T := lt_of_not_ge h
  let : IsEmpty (F.slice T).carrier :=
    F.extinction_permanent a T ha (F.surgery_times_subset hT) haT.le inferInstance
  let E := F.vanishing_event T hT
  let t := max a E.tMinus
  have ht : t ∈ Ico E.tMinus T :=
    ⟨le_max_right _ _, max_lt haT E.tMinus_lt⟩
  have htD : t ∈ F.time_domain :=
    F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
      ⟨E.tMinus_nonnegative.trans ht.1, ht.2.le⟩
  let : IsEmpty (F.slice t).carrier :=
    F.extinction_permanent a t ha htD (le_max_left _ _) inferInstance
  obtain ⟨x⟩ := E.pre_nonempty
  exact isEmptyElim (E.pre_identify ⟨t, ht⟩ x)

theorem nonemptySurgeryTime_lt_empty (F : SurgeryFlowData.{u}) {a T : ℝ}
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier]
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier] : T < a := by
  refine lt_of_le_of_ne (F.surgeryTime_le_empty ha hT) ?_
  intro h
  subst T
  obtain ⟨x⟩ := (inferInstance : Nonempty (F.slice a).carrier)
  exact isEmptyElim x

theorem surgeryTimes_finite_of_empty (F : SurgeryFlowData.{u}) {a : ℝ}
    (ha : a ∈ F.time_domain) [IsEmpty (F.slice a).carrier] :
    F.surgery_times.Finite := by
  apply (F.surgery_times_finite_on_compact isCompact_Icc
    (F.time_domain_interval.out F.zero_mem ha)).subset
  intro t ht
  exact ⟨ht, F.time_domain_nonnegative (F.surgery_times_subset ht),
    F.surgeryTime_le_empty ha ht⟩

end PoincareConjecture.SurgeryFlowData
