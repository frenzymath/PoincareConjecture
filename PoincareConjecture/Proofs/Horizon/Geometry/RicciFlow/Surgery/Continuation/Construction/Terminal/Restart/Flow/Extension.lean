import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Restart.Flow.Assembly


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.Surgery.TerminalRestart

variable {F : SurgeryFlowData.{u}} {T : ℝ} (I : RepairedContinuationInput F T)
  (C : GeneralizedSliceCarrier.{u}) {B : ℝ≥0∞}
  (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})
  (E : SurgeryEventData F.standard_initial F.local_constants F.parameters
    (Splice.slice F T C R) (Splice.metric F T C R) T)
  [Nonempty C.carrier] (hC : IsCompact (univ : Set C.carrier))
  (hRP : SurgeryNoTwoSidedProjectivePlane C) (hB : ENNReal.ofReal T < B)
  (hblow : B ≠ ⊤ → ∀ L s : ℝ, s < B.toReal →
    ∃ t ∈ Ioo (max T s) B.toReal, ∃ x : C.carrier,
      L < (R.connection t).curvatureTensorNorm x)
  (hE : ∀ a b hab hJ hfree, ∀ s t : ℝ, ∀ hs : s ∈ Icc a b, ∀ ht : t ∈ Icc a b,
    ∀ hs' : s ∈ Ico E.tMinus T, ∀ ht' : t ∈ Ico E.tMinus T, ∀ x,
      (Splice.regularSlab F T C R I.time_domain_eq hab hJ hfree).transport
        ⟨s, hs⟩ ⟨t, ht⟩ (E.pre_identify ⟨s, hs'⟩ x) = E.pre_identify ⟨t, ht'⟩ x)

def extension : SurgeryFlowExtension F where
  extended := flow I C R E hC hRP hB hblow hE
  old_times := old_times I hB
  standard_initial_eq := rfl
  local_constants_eq := rfl
  parameters_eq := rfl
  identify := fun t ht => Splice.identifyBefore F T C R t (I.time_domain_eq ▸ ht).2
  metric_pullback := fun t ht x v w =>
    Splice.identifyBefore_metric F T C R t (I.time_domain_eq ▸ ht).2 x v w
  old_surgery_times := by
    intro t ht
    change t ∈ insert T F.surgery_times ↔ t ∈ F.surgery_times
    simp only [mem_insert_iff, (I.time_domain_eq ▸ ht).2.ne, false_or]
  ordinary_compatibility := by
    intro a b hab hJ hfree hJ' hfree' s t x
    exact Splice.regularSlab_transport_before F T C R I.time_domain_eq hab hJ' hfree'
      (I.time_domain_eq ▸ hJ ⟨hab.le, le_rfl⟩).2 hJ hfree s t x
  old_event_reference := by
    intro U hU _hne _hne' hU'
    change (event I C R E U hU').tMinus = (F.event U hU).tMinus
    rw [event_old I C R E U hU hU']
    rfl
  old_retained_post := by
    intro U hU hU' _hne _hne'
    change _ = (event I C R E U hU').retained_post
    rw [event_old I C R E U hU hU']
    exact Splice.oldEvent_retained_post_image F T C R U hU
      (I.time_domain_eq ▸ F.surgery_times_subset hU).2
  old_retained_pre := by
    intro U hU hU' _hne _hne'
    have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hU).2
    change ∀ (t : Ico (F.event U hU).tMinus U) (ht : t.1 ∈ F.time_domain)
      (ht' : t.1 ∈ Ico (event I C R E U hU').tMinus U),
      (fun x => ((event I C R E U hU').pre_identify ⟨t.1, ht'⟩).symm
        (Splice.identifyBefore F T C R t.1 (I.time_domain_eq ▸ ht).2
          ((F.event U hU).pre_identify t x))) '' (F.event U hU).retained_pre =
        (event I C R E U hU').retained_pre
    rw [event_old I C R E U hU hU']
    intro t ht ht'
    refine (Set.image_congr (fun x _ => ?_)).trans
      (Splice.oldEvent_retained_pre_image F T C R U hU hUT)
    exact Splice.oldEvent_pre_inverse F T C R U hU hUT t x
  old_retention := by
    intro U hU hU' _hne _hne'
    have hUT : U < T := (I.time_domain_eq ▸ F.surgery_times_subset hU).2
    change ∀ (t : Ico (F.event U hU).tMinus U) (ht : t.1 ∈ F.time_domain)
      (ht' : t.1 ∈ Ico (event I C R E U hU').tMinus U),
      ∀ x ∈ (F.event U hU).retained_pre,
      Splice.identifyBefore F T C R U hUT ((F.event U hU).retention.map x) =
        (event I C R E U hU').retention.map
          (((event I C R E U hU').pre_identify ⟨t.1, ht'⟩).symm
            (Splice.identifyBefore F T C R t.1 (I.time_domain_eq ▸ ht).2
              ((F.event U hU).pre_identify t x)))
    rw [event_old I C R E U hU hU']
    intro t ht ht' x _hx
    exact (Splice.oldEvent_retention_map F T C R U hU hUT x).symm.trans
      (congrArg (Splice.oldEvent F T C R U hU hUT).retention.map
        (Splice.oldEvent_pre_inverse F T C R U hU hUT t x).symm)
  old_vanishing_reference := by
    intro U hU _he _he' _hU'
    obtain ⟨x⟩ := I.slices_nonempty U (F.surgery_times_subset hU)
    exact isEmptyElim x

theorem old_event_preservation :
    M33OldEventDataPreservation (extension I C R E hC hRP hB hblow hE) := by
  constructor
  · intro U hU _hne _hne' hU'
    change M33NonemptyEventDataPreservation (F.event U hU) (event I C R E U hU')
    rw [event_old I C R E U hU hU']
    exact Splice.oldEvent_preservation F T C R U hU
      (I.time_domain_eq ▸ F.surgery_times_subset hU).2
  · intro U hU _he _he' _hU'
    obtain ⟨x⟩ := I.slices_nonempty U (F.surgery_times_subset hU)
    exact isEmptyElim x

end PoincareConjecture.Surgery.TerminalRestart
