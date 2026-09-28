import PoincareConjecture.Proofs.M51.GlobalSlabCoherence
import PoincareConjecture.Proofs.M51.SlabTransport

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51.CompletedStageChain

variable {S : RepairedControlledSchedulesData.{u}}
  {N : RepairedNoncollapseInductionData S}
  {C : RepairedCanonicalInductionData S N}
  {F0 : SurgeryFlowData.{u}} {k : Nat}
  (Q : CompletedStageChain S N C F0 k)

theorem stage_surgeryFree_of_global (n : Nat) {a b : Real}
    (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b)) :
    Disjoint (Q.flow n).surgery_times (Ioc a b) :=
  hfree.mono_left (fun _ ht => Q.surgery_mem_global n ht)

theorem globalSlab_time {a b : Real} (hJ : Icc a b ⊆ Ici 0)
    {t : Real} (ht : t ∈ Icc a b) :
    t ∈ (Q.flow (Q.representativeIndex b)).time_domain :=
  Q.mem_time_domain_of_lt_horizon _ (hJ ht)
    (ht.2.trans_lt (Q.representative_horizon b))

noncomputable def globalSourceSlab (a b : Real) (hab : a < b)
    (hJ : Icc a b ⊆ Ici 0) (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b)) :
    SurgeryRegularSlab (Q.flow (Q.representativeIndex b)).slice
      (Q.flow (Q.representativeIndex b)).metric a b :=
  (Q.flow (Q.representativeIndex b)).regular_slabs a b hab
    (fun _ ht => Q.globalSlab_time hJ ht) (Q.stage_surgeryFree_of_global _ hfree)

noncomputable def globalSlabPullback (a b : Real) (hab : a < b)
    (hJ : Icc a b ⊆ Ici 0) (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b)) :
    SurgeryRegularSlab.PullbackData (Q.globalSourceSlab a b hab hJ hfree)
      Q.globalSlice Q.globalMetric
      (Q.globalIdentify (Q.representativeIndex b) a
        (Q.globalSlab_time hJ ⟨le_rfl, hab.le⟩)).symm :=
  SurgeryRegularSlab.PullbackData.ofIsometry (Q.globalSourceSlab a b hab hJ hfree)
    Q.globalSlice Q.globalMetric
    (Q.globalIdentify (Q.representativeIndex b) a
      (Q.globalSlab_time hJ ⟨le_rfl, hab.le⟩)).symm
    (fun t => Q.globalIdentify (Q.representativeIndex b) t.1
      (Q.globalSlab_time hJ t.2))
    (fun x => Diffeomorph.apply_symm_apply _ x)
    (fun t x v w => Q.globalIdentify_metric (Q.representativeIndex b) t.1
      (Q.globalSlab_time hJ t.2) x v w)

noncomputable def globalSlab (a b : Real) (hab : a < b)
    (hJ : Icc a b ⊆ Ici 0) (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b)) :
    SurgeryRegularSlab Q.globalSlice Q.globalMetric a b :=
  SurgeryRegularSlab.pullback (Q.globalSourceSlab a b hab hJ hfree)
    (Q.globalSlabPullback a b hab hJ hfree)

theorem globalSlab_transport (a b : Real) (hab : a < b)
    (hJ : Icc a b ⊆ Ici 0) (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b))
    (s t : Icc a b) (x : (Q.globalSlice s.1).carrier) :
    (Q.globalSlab a b hab hJ hfree).transport s t x =
      Q.globalIdentify (Q.representativeIndex b) t.1 (Q.globalSlab_time hJ t.2)
        ((Q.globalSourceSlab a b hab hJ hfree).transport s t
          ((Q.globalIdentify (Q.representativeIndex b) s.1
            (Q.globalSlab_time hJ s.2)).symm x)) :=
  SurgeryRegularSlab.pullback_transport_symm _ _ s t x

theorem globalSlab_compare (a b : Real) (hab : a < b)
    (hJ : Icc a b ⊆ Ici 0) (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b))
    (n : Nat) (c d : Real) (hcd : c < d)
    (hK : Icc c d ⊆ (Q.flow n).time_domain)
    (hfree' : Disjoint (Q.flow n).surgery_times (Ioc c d))
    (s t : Real) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Icc c d) (ht' : t ∈ Icc c d)
    (x : ((Q.flow n).slice s).carrier) :
    (Q.globalSlab a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩
      (Q.globalIdentify n s (hK hs') x) =
        Q.globalIdentify n t (hK ht')
          (((Q.flow n).regular_slabs c d hcd hK hfree').transport
            ⟨s, hs'⟩ ⟨t, ht'⟩ x) := by
  rw [Q.globalSlab_transport]
  exact Q.globalIdentify_slab_coherent (Q.representativeIndex b) n a b c d
    hab (fun _ ht => Q.globalSlab_time hJ ht) (Q.stage_surgeryFree_of_global _ hfree)
    hcd hK hfree' s t hs ht hs' ht' _ x
    (Diffeomorph.apply_symm_apply _ _)

theorem globalSlab_coherent (a b c d : Real)
    (hab : a < b) (hJ : Icc a b ⊆ Ici 0)
    (hfree : Disjoint Q.globalSurgeryTimes (Ioc a b))
    (hcd : c < d) (hK : Icc c d ⊆ Ici 0)
    (hfree' : Disjoint Q.globalSurgeryTimes (Ioc c d))
    (s t : Real) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Icc c d) (ht' : t ∈ Icc c d)
    (x : (Q.globalSlice s).carrier) :
    (Q.globalSlab a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩ x =
      (Q.globalSlab c d hcd hK hfree').transport ⟨s, hs'⟩ ⟨t, ht'⟩ x := by
  rw [Q.globalSlab_transport, Q.globalSlab_transport]
  apply Q.globalIdentify_slab_coherent (Q.representativeIndex b) (Q.representativeIndex d)
    a b c d hab (fun _ ht => Q.globalSlab_time hJ ht)
    (Q.stage_surgeryFree_of_global _ hfree)
    hcd (fun _ ht => Q.globalSlab_time hK ht) (Q.stage_surgeryFree_of_global _ hfree')
    s t hs ht hs' ht'
  rw [Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply]

end PoincareConjecture.M51.CompletedStageChain
