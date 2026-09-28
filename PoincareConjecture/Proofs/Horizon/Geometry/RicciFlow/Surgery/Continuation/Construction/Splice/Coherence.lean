import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Splice.Family

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Surgery.Splice

variable (F : SurgeryFlowData.{u}) (T : ℝ) (C : GeneralizedSliceCarrier.{u})
  {B : ℝ≥0∞} (R : RicciFlow 3 C.carrier {t : ℝ | T ≤ t ∧ ENNReal.ofReal t < B})

theorem regularSlab_transport_coherent (hF : F.time_domain = Set.Ico 0 T)
    (a b c d : ℝ) (hab : a < b)
    (hJ : Set.Icc a b ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree : Disjoint (eventTimes F T) (Set.Ioc a b)) (hcd : c < d)
    (hK : Set.Icc c d ⊆ {t : ℝ | 0 ≤ t ∧ ENNReal.ofReal t < B})
    (hfree' : Disjoint (eventTimes F T) (Set.Ioc c d))
    (s t : ℝ) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b)
    (hs' : s ∈ Set.Icc c d) (ht' : t ∈ Set.Icc c d)
    (x : (slice F T C R s).carrier) :
    (regularSlab F T C R hF hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩ x =
      (regularSlab F T C R hF hcd hK hfree').transport ⟨s, hs'⟩ ⟨t, ht'⟩ x := by
  rcases slab_side F T hfree with hb | ha
  · rcases slab_side F T hfree' with hd | hc
    · have hold : Set.Icc a b ⊆ F.time_domain := by
        intro q hq
        rw [hF]
        exact ⟨(hJ hq).1, hq.2.trans_lt hb⟩
      have hold' : Set.Icc c d ⊆ F.time_domain := by
        intro q hq
        rw [hF]
        exact ⟨(hK hq).1, hq.2.trans_lt hd⟩
      have hfreeold := hfree.mono_left (Set.subset_insert T F.surgery_times)
      have hfreeold' := hfree'.mono_left (Set.subset_insert T F.surgery_times)
      obtain ⟨y, rfl⟩ := (identifyBefore F T C R s (hs.2.trans_lt hb)).surjective x
      exact (regularSlab_transport_before F T C R hF hab hJ hfree hb hold hfreeold
        ⟨s, hs⟩ ⟨t, ht⟩ y).trans
        ((congrArg (identifyBefore F T C R t (ht.2.trans_lt hb))
          (F.slab_transport_coherent a b c d hab hold hfreeold hcd hold' hfreeold'
            s t hs ht hs' ht' y)).trans
          (regularSlab_transport_before F T C R hF hcd hK hfree' hd hold' hfreeold'
            ⟨s, hs'⟩ ⟨t, ht'⟩ y).symm)
    · exact False.elim ((not_lt_of_ge (hc.trans hs'.1)) (hs.2.trans_lt hb))
  · rcases slab_side F T hfree' with hd | hc
    · exact False.elim ((not_lt_of_ge (ha.trans hs.1)) (hs'.2.trans_lt hd))
    · obtain ⟨y, rfl⟩ := (identifyAfter F T C R s (ha.trans hs.1)).surjective x
      exact (regularSlab_transport_after F T C R hF hab hJ hfree ha
        ⟨s, hs⟩ ⟨t, ht⟩ y).trans
        (regularSlab_transport_after F T C R hF hcd hK hfree' hc
          ⟨s, hs'⟩ ⟨t, ht'⟩ y).symm

end PoincareConjecture.Surgery.Splice
