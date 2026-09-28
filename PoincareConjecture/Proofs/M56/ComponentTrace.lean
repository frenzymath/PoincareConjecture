import PoincareConjecture.Proofs.M56.EventGap
import PoincareConjecture.Proofs.M56.Mathlib.ComponentClasses

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

structure M56ComponentTrace (F : SurgeryFlowData.{u}) (T : ℝ) where
  time_subset : Icc 0 T ⊆ F.time_domain
  point : ∀ s : Icc (0 : ℝ) T, (F.slice s.1).carrier
  regular : ∀ (a b : ℝ) (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (s t : Icc (0 : ℝ) T) (hs : s.1 ∈ Icc a b) (ht : t.1 ∈ Icc a b),
    ConnectedComponents.mk
        (((F.regular_slabs a b hab hJ hfree).identify ⟨s.1, hs⟩).symm (point s)) =
      ConnectedComponents.mk
        (((F.regular_slabs a b hab hJ hfree).identify ⟨t.1, ht⟩).symm (point t))
  inherited : ∀ (s : Icc (0 : ℝ) T) (hs : s.1 ∈ F.surgery_times)
    (hpost : Nonempty (F.slice s.1).carrier), letI := hpost
    ∃ x : (F.slice (F.event s.1 hs).tMinus).carrier,
      x ∈ connectedComponent
        (point ⟨(F.event s.1 hs).tMinus,
          (F.event s.1 hs).tMinus_nonnegative,
          (F.event s.1 hs).tMinus_lt.le.trans s.2.2⟩) ∧
      x ∈ interior (F.event s.1 hs).retained_pre ∧
      (F.event s.1 hs).retention.map x ∈ connectedComponent (point s)

theorem m56Slab_pullback_eq (F : SurgeryFlowData.{u})
    {a b c d : ℝ} (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (hcd : c < d) (hK : Icc c d ⊆ F.time_domain)
    (hfree' : Disjoint F.surgery_times (Ioc c d))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Icc c d) (ht' : t ∈ Icc c d)
    (x : (F.slice c).carrier) :
    ((F.regular_slabs a b hab hJ hfree).identify ⟨s, hs⟩).symm
        ((F.regular_slabs c d hcd hK hfree').identify ⟨s, hs'⟩ x) =
      ((F.regular_slabs a b hab hJ hfree).identify ⟨t, ht⟩).symm
        ((F.regular_slabs c d hcd hK hfree').identify ⟨t, ht'⟩ x) := by
  have h := F.slab_transport_coherent a b c d hab hJ hfree hcd hK hfree'
    s t hs ht hs' ht' ((F.regular_slabs c d hcd hK hfree').identify ⟨s, hs'⟩ x)
  simp only [SurgeryRegularSlab.transport, Diffeomorph.symm_apply_apply] at h
  have hinv := congrArg ((F.regular_slabs a b hab hJ hfree).identify ⟨t, ht⟩).symm h
  simpa only [Diffeomorph.symm_apply_apply] using hinv

theorem m56Event_pullback_eq (F : SurgeryFlowData.{u})
    {T : ℝ} (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Ico (F.event T hT).tMinus T)
    (ht' : t ∈ Ico (F.event T hT).tMinus T)
    (x : (F.slice (F.event T hT).tMinus).carrier) :
    ((F.regular_slabs a b hab hJ hfree).identify ⟨s, hs⟩).symm
        ((F.event T hT).pre_identify ⟨s, hs'⟩ x) =
      ((F.regular_slabs a b hab hJ hfree).identify ⟨t, ht⟩).symm
        ((F.event T hT).pre_identify ⟨t, ht'⟩ x) := by
  have h := F.event_slab_compatibility T hT a b hab hJ hfree s t hs ht hs' ht' x
  have hinv := congrArg ((F.regular_slabs a b hab hJ hfree).identify ⟨t, ht⟩).symm h
  simpa only [SurgeryRegularSlab.transport, Diffeomorph.symm_apply_apply] using hinv

end PoincareConjecture
