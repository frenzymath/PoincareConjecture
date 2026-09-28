import PoincareConjecture.Proofs.M56.RegularTrace
import PoincareConjecture.Proofs.M56.EventTrace
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.FiniteEventInduction









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



noncomputable def m56Trace_zero (F : SurgeryFlowData.{u}) (x : (F.slice 0).carrier) :
    M56ComponentTrace F 0 where
  time_subset := by
    intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    exact ht0.symm ▸ F.zero_mem
  point s := (show s.1 = 0 from le_antisymm s.2.2 s.2.1).symm ▸ x
  regular := by
    intro a b hab hJ hfree s t hs ht
    have hst : s = t := Subtype.ext (le_antisymm
      (s.2.2.trans t.2.1) (t.2.2.trans s.2.1))
    subst t
    rfl
  inherited := by
    intro s hs _
    exact False.elim (F.zero_not_surgery ((le_antisymm s.2.2 s.2.1) ▸ hs))



theorem m56Trace_exists (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.time_domain)
    (x : (F.slice T).carrier) :
    ∃ P : M56ComponentTrace F T,
      x ∈ connectedComponent (P.point ⟨T, F.time_domain_nonnegative hT, le_rfl⟩) := by
  let Q := fun t : ℝ => ∀ ht : t ∈ F.time_domain, ∀ y : (F.slice t).carrier,
    ∃ P : M56ComponentTrace F t,
      y ∈ connectedComponent (P.point ⟨t, F.time_domain_nonnegative ht, le_rfl⟩)
  have hJ : Icc 0 T ⊆ F.time_domain := F.time_domain_interval.out F.zero_mem hT
  have hfinite : (F.surgery_times ∩ Ioc 0 T).Finite :=
    (F.surgery_times_finite_on_compact isCompact_Icc hJ).subset
      (inter_subset_inter_right _ Ioc_subset_Icc_self)
  have hQ : Q T := by
    apply Proofs.M46.finite_event_forward_induction (F.time_domain_nonnegative hT)
      hfinite Q
    · intro _ y
      exact ⟨m56Trace_zero F y, mem_connectedComponent⟩
    · intro a ha b hb hab hfree hA hB y
      rcases hab.eq_or_lt with rfl | hab
      · exact hA hB y
      have hK : Icc a b ⊆ F.time_domain :=
        fun t ht => hJ ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
      let S := F.regular_slabs a b hab hK hfree
      let z := (S.identify ⟨b, hab.le, le_rfl⟩).symm y
      obtain ⟨P, hP⟩ := hA (hJ ha) z
      refine ⟨m56Trace_regularExtension P ha.1 hab hK hfree z hP, ?_⟩
      rw [m56Trace_regularExtension_terminal]
      change y ∈ connectedComponent (S.identify ⟨b, hab.le, le_rfl⟩
        ((S.identify ⟨b, hab.le, le_rfl⟩).symm y))
      rw [Diffeomorph.apply_symm_apply]
      exact mem_connectedComponent
    · intro s hs ih _ y
      let : Nonempty (F.slice s).carrier := ⟨y⟩
      let E := F.event s hs.1
      obtain ⟨z, hz, hzy⟩ := m56Event_component_meets_retainedInterior E y
      have hE : E.tMinus ∈ F.time_domain := F.time_domain_interval.out F.zero_mem
        (F.surgery_times_subset hs.1) ⟨E.tMinus_nonnegative, E.tMinus_lt.le⟩
      obtain ⟨P, hP⟩ := ih E.tMinus ⟨E.tMinus_nonnegative, E.tMinus_lt⟩ hE z
      refine ⟨m56Trace_eventExtension hs.1 P z hP y hz hzy, ?_⟩
      rw [m56Trace_eventExtension_terminal]
      exact mem_connectedComponent
  exact hQ hT x

end PoincareConjecture
