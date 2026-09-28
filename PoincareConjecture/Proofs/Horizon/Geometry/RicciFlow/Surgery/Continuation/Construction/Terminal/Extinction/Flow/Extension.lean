import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Flow.Assembly









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

def extension : SurgeryFlowExtension F where
  extended := flow I V hV
  old_times := fun _ ht => ⟨F.time_domain_nonnegative ht, ENNReal.ofReal_lt_top⟩
  standard_initial_eq := rfl
  local_constants_eq := rfl
  parameters_eq := rfl
  identify := fun t ht => Splice.identifyBefore F T (emptyCarrier (F.slice 0))
    (emptyFlow (F.metric 0) T) t (I.time_domain_eq ▸ ht).2
  metric_pullback := fun t ht x v w => Splice.identifyBefore_metric F T
    (emptyCarrier (F.slice 0)) (emptyFlow (F.metric 0) T) t
      (I.time_domain_eq ▸ ht).2 x v w
  old_surgery_times := by
    intro t ht
    change t ∈ insert T F.surgery_times ↔ t ∈ F.surgery_times
    simp only [mem_insert_iff, (I.time_domain_eq ▸ ht).2.ne, false_or]
  ordinary_compatibility := by
    intro a b hab hJ hfree hJ' hfree' s t x
    exact Splice.regularSlab_transport_before F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) I.time_domain_eq hab hJ' hfree'
        (I.time_domain_eq ▸ hJ ⟨hab.le, le_rfl⟩).2 hJ hfree s t x
  old_event_reference := by
    intro U hU _hne _hne' hU'
    rfl
  old_retained_post := by
    intro U hU hU' _hne _hne'
    exact Splice.oldEvent_retained_post_image F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hU (I.time_domain_eq ▸ F.surgery_times_subset hU).2
  old_retained_pre := by
    intro U hU hU' _hne _hne' t ht ht'
    have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hU).2
    refine (Set.image_congr (fun x _ => ?_)).trans
      (Splice.oldEvent_retained_pre_image F T (emptyCarrier (F.slice 0))
        (emptyFlow (F.metric 0) T) U hU hUT)
    exact Splice.oldEvent_pre_inverse F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hU hUT t x
  old_retention := by
    intro U hU hU' _hne _hne' t ht ht' x _hx
    have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hU).2
    exact (Splice.oldEvent_retention_map F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hU hUT x).symm.trans
        (congrArg (Splice.oldEvent F T (emptyCarrier (F.slice 0))
          (emptyFlow (F.metric 0) T) U hU hUT).retention.map
            (Splice.oldEvent_pre_inverse F T (emptyCarrier (F.slice 0))
              (emptyFlow (F.metric 0) T) U hU hUT t x).symm)
  old_vanishing_reference := by
    intro U hU _he _he' _hU'
    obtain ⟨x⟩ := I.slices_nonempty U (F.surgery_times_subset hU)
    exact isEmptyElim x

theorem old_event_preservation : M33OldEventDataPreservation (extension I V hV) := by
  constructor
  · intro U hU _hne _hne' hU'
    exact Splice.oldEvent_preservation F T (emptyCarrier (F.slice 0))
      (emptyFlow (F.metric 0) T) U hU (I.time_domain_eq ▸ F.surgery_times_subset hU).2
  · intro U hU _he _he' _hU'
    obtain ⟨x⟩ := I.slices_nonempty U (F.surgery_times_subset hU)
    exact isEmptyElim x

end PoincareConjecture.Surgery.Extinction
