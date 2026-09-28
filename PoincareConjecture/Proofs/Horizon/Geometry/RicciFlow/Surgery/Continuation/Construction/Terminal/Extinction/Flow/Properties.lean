import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Extension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.Extinction

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (V : SurgeryVanishingEventData F.parameters F.slice F.metric T)
  (hV : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ Ico V.tMinus T, ∀ ht' : t ∈ Ico V.tMinus T, ∀ x,
      (F.regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
        (V.pre_identify ⟨s, hs'⟩ x) = V.pre_identify ⟨t, ht'⟩ x)

theorem time_domain_eq : (flow I V hV).time_domain = Ici 0 := by
  ext t
  exact and_iff_left ENNReal.ofReal_lt_top

theorem surgery_at_terminal : T ∈ (flow I V hV).surgery_times := mem_insert _ _

theorem no_later_surgery (t : ℝ) (ht : T < t) : t ∉ (flow I V hV).surgery_times := by
  intro hevent
  rcases mem_insert_iff.mp hevent with hEq | hold
  · exact ht.ne' hEq
  · exact (ht.trans (I.time_domain_eq ▸ F.surgery_times_subset hold).2).false

theorem flow_empty_after (t : ℝ) (ht : T ≤ t) : IsEmpty ((flow I V hV).slice t).carrier :=
  slice_empty_after F T ht

theorem post_terminal_interval : ∃ d : ℝ, 0 < d ∧
    Ioo T (T + d) ⊆ (flow I V hV).time_domain ∧
    Disjoint (flow I V hV).surgery_times (Ioo T (T + d)) := by
  refine ⟨1, by norm_num, ?_, ?_⟩
  · intro t ht
    exact ⟨(I.terminal_pos.trans ht.1).le, ENNReal.ofReal_lt_top⟩
  · exact disjoint_left.mpr (fun t ht hti => no_later_surgery I V hV t hti.1 ht)

theorem pinched : SurgeryFlowPinched (flow I V hV) := by
  intro t ht
  by_cases h : t < T
  · have hcopy (p q : SurgeryEventRebuild.SliceMetric.{u}) (hpq : p = q)
        (D : LeviCivitaData p.2) (hD : SurgeryPinchedAt D t) :
        SurgeryPinchedAt
          (SurgeryEventRebuild.relabel (C := fun z => LeviCivitaData z.2) hpq D) t := by
      subst q
      exact hD
    change SurgeryPinchedAt (connection (F := F) (T := T) t) t
    unfold connection Splice.connection
    rw [dif_pos h]
    exact hcopy ⟨F.slice t, F.metric t⟩ _
      (Splice.family_before F T (emptyCarrier (F.slice 0))
        (emptyFlow (F.metric 0) T) h).symm (F.connection t)
      (I.pinched t (I.time_domain_eq ▸ (show t ∈ Ico 0 T from ⟨ht.1, h⟩)))
  · let := flow_empty_after I V hV t (le_of_not_gt h)
    exact ⟨ht.1, fun x => isEmptyElim x, fun x => isEmptyElim x⟩

theorem vanishing_event_eq [IsEmpty ((flow I V hV).slice T).carrier] :
    (flow I V hV).vanishing_event T (surgery_at_terminal I V hV) =
      Splice.vanishingEvent F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) V := rfl

theorem vanishing_terminal_policy [IsEmpty ((flow I V hV).slice T).carrier]
    (h : SurgeryVanishingEventTerminalPolicy V) :
    SurgeryVanishingEventTerminalPolicy
      ((flow I V hV).vanishing_event T (surgery_at_terminal I V hV)) :=
  V.copyBefore_terminalPolicy
    (past := fun q => ⟨F.slice q, F.metric q⟩)
    (future := Splice.family F T (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T))
    (fun _q hq => (Splice.family_before F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) hq.2).symm) h

end PoincareConjecture.Surgery.Extinction
