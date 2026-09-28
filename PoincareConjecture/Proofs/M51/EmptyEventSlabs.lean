import PoincareConjecture.Proofs.M51.EmptyEvents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier]

theorem event_slab_compatibility (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (slice F a T).carrier] (p q : ℝ) (hpq : p < q)
    (hJ : Icc p q ⊆ Ici 0) (hfree : Disjoint F.surgery_times (Ioc p q))
    (s t : ℝ) (hs : s ∈ Icc p q) (ht : t ∈ Icc p q)
    (hs' : s ∈ Ico (event F ha T hT).tMinus T)
    (ht' : t ∈ Ico (event F ha T hT).tMinus T)
    (x : (slice F a (event F ha T hT).tMinus).carrier) :
    (regularSlab F ha p q hpq hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      ((event F ha T hT).pre_identify ⟨s, hs'⟩ x) =
        (event F ha T hT).pre_identify ⟨t, ht'⟩ x := by
  let : Nonempty (F.slice T).carrier := by
    simpa only [slice, event_clock F ha T hT T le_rfl] using
      (inferInstance : Nonempty (slice F a T).carrier)
  let E := F.event T hT
  let c := M51EventCopy.identify F.slice (fun z => min z a) E.tMinus
    (event_clock F ha T hT E.tMinus E.tMinus_lt.le)
  let y := c.symm x
  have hy : HEq x y := (M51EventCopy.identify_symm_apply_heq F.slice
    (fun z => min z a) E.tMinus
    (event_clock F ha T hT E.tMinus E.tMinus_lt.le) x).symm
  have hqa := regularSlab_end_le F ha p q hpq hJ hfree hs
    ((event F ha T hT).pre_identify ⟨s, hs'⟩ x)
  have hOld : Icc p q ⊆ F.time_domain := fun z hz =>
    F.time_domain_interval.out F.zero_mem ha ⟨hJ hz, hz.2.trans hqa⟩
  have hleft := regularSlab_transport_heq F ha p q hpq hJ hfree hqa hOld
    ⟨s, hs⟩ ⟨t, ht⟩ (event_pre_identify_heq F ha T hT ⟨s, hs'⟩ hy)
  have hmiddle := F.event_slab_compatibility T hT p q hpq hOld hfree
    s t hs ht hs' ht' y
  have hright := event_pre_identify_heq F ha T hT ⟨t, ht'⟩ hy
  exact eq_of_heq ((hleft.trans (heq_of_eq hmiddle)).trans hright.symm)

theorem vanishing_slab_compatibility (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (slice F a T).carrier] (p q : ℝ) (hpq : p < q)
    (hJ : Icc p q ⊆ Ici 0) (hfree : Disjoint F.surgery_times (Ioc p q))
    (s t : ℝ) (hs : s ∈ Icc p q) (ht : t ∈ Icc p q)
    (hs' : s ∈ Ico (vanishingEvent F ha T hT).tMinus T)
    (ht' : t ∈ Ico (vanishingEvent F ha T hT).tMinus T)
    (x : (slice F a (vanishingEvent F ha T hT).tMinus).carrier) :
    (regularSlab F ha p q hpq hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      ((vanishingEvent F ha T hT).pre_identify ⟨s, hs'⟩ x) =
        (vanishingEvent F ha T hT).pre_identify ⟨t, ht'⟩ x := by
  let : IsEmpty (F.slice T).carrier := by
    simpa only [slice, event_clock F ha T hT T le_rfl] using
      (inferInstance : IsEmpty (slice F a T).carrier)
  let E := F.vanishing_event T hT
  let c := M51EventCopy.identify F.slice (fun z => min z a) E.tMinus
    (event_clock F ha T hT E.tMinus E.tMinus_lt.le)
  let y := c.symm x
  have hy : HEq x y := (M51EventCopy.identify_symm_apply_heq F.slice
    (fun z => min z a) E.tMinus
    (event_clock F ha T hT E.tMinus E.tMinus_lt.le) x).symm
  have hqa := regularSlab_end_le F ha p q hpq hJ hfree hs
    ((vanishingEvent F ha T hT).pre_identify ⟨s, hs'⟩ x)
  have hOld : Icc p q ⊆ F.time_domain := fun z hz =>
    F.time_domain_interval.out F.zero_mem ha ⟨hJ hz, hz.2.trans hqa⟩
  have hleft := regularSlab_transport_heq F ha p q hpq hJ hfree hqa hOld
    ⟨s, hs⟩ ⟨t, ht⟩ (vanishingEvent_pre_identify_heq F ha T hT ⟨s, hs'⟩ hy)
  have hmiddle := F.vanishing_slab_compatibility T hT p q hpq hOld hfree
    s t hs ht hs' ht' y
  have hright := vanishingEvent_pre_identify_heq F ha T hT ⟨t, ht'⟩ hy
  exact eq_of_heq ((hleft.trans (heq_of_eq hmiddle)).trans hright.symm)

end PoincareConjecture.M51Empty
