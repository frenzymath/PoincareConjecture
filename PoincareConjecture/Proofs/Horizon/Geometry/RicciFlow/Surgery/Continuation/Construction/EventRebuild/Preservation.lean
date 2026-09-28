import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.EventRebuild.Family

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem M33OldEventDataPreservation.of_rebuildPast
    {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
    (hSlice : ∀ t ∈ F.time_domain, F.slice t = E.extended.slice t)
    (hMetric : ∀ t ∈ F.time_domain, HEq (F.metric t) (E.extended.metric t))
    (hEvent : ∀ T hT [Nonempty (F.slice T).carrier]
      [Nonempty (E.extended.slice T).carrier], ∀ hT' : T ∈ E.extended.surgery_times,
      HEq (E.extended.event T hT') ((F.event T hT).rebuildPast
        (fun t ht => hSlice t
          (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht))
        (fun t ht => hMetric t
          (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht))))
    (hVanishing : ∀ T hT [IsEmpty (F.slice T).carrier]
      [IsEmpty (E.extended.slice T).carrier], ∀ hT' : T ∈ E.extended.surgery_times,
      HEq (E.extended.vanishing_event T hT') ((F.vanishing_event T hT).rebuildPast
        (fun t ht => hSlice t
          (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht))
        (fun t ht => hMetric t
          (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht)))) :
    M33OldEventDataPreservation E := by
  constructor
  · intro T hT hOld hNew hT'
    exact (F.event T hT).rebuildPast_preservation_of_heq
      (fun t ht => hSlice t
        (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht))
      (fun t ht => hMetric t
        (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht))
      (E.extended.event T hT') E.standard_initial_eq E.local_constants_eq E.parameters_eq
      (hEvent T hT hT')
  · intro T hT hOld hNew hT'
    exact (F.vanishing_event T hT).rebuildPast_preservation_of_heq
      (fun t ht => hSlice t
        (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht))
      (fun t ht => hMetric t
        (F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT) ht))
      (E.extended.vanishing_event T hT') E.parameters_eq (hVanishing T hT hT')

end PoincareConjecture
