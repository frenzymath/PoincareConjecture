import PoincareConjecture.Proofs.M51.GlobalRepresentatives

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

theorem stage_surgeryFreeTo (n m : Nat) (hnm : n <= m) {a b : Real}
    (hJ : Icc a b ⊆ (Q.flow n).time_domain)
    (hfree : Disjoint (Q.flow n).surgery_times (Ioc a b)) :
    Disjoint (Q.flow m).surgery_times (Ioc a b) := by
  refine disjoint_left.mpr ?_
  intro t ht hs
  have htF := hJ ⟨hs.1.le, hs.2⟩
  have hiff := ComposedExtension.oldSurgeryTimeTo
    (Q.extensionBetween n m hnm) (Q.extensionBetween_eq n m hnm) t htF
  exact disjoint_left.mp hfree (hiff.mp ht) hs

theorem globalIdentify_slab_coherent (n m : Nat) (a b c d : Real)
    (hab : a < b) (hJ : Icc a b ⊆ (Q.flow n).time_domain)
    (hfree : Disjoint (Q.flow n).surgery_times (Ioc a b))
    (hcd : c < d) (hK : Icc c d ⊆ (Q.flow m).time_domain)
    (hfree' : Disjoint (Q.flow m).surgery_times (Ioc c d))
    (s t : Real) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hs' : s ∈ Icc c d) (ht' : t ∈ Icc c d)
    (x : ((Q.flow n).slice s).carrier) (y : ((Q.flow m).slice s).carrier)
    (hxy : Q.globalIdentify n s (hJ hs) x = Q.globalIdentify m s (hK hs') y) :
    Q.globalIdentify n t (hJ ht)
        (((Q.flow n).regular_slabs a b hab hJ hfree).transport ⟨s, hs⟩ ⟨t, ht⟩ x) =
      Q.globalIdentify m t (hK ht')
        (((Q.flow m).regular_slabs c d hcd hK hfree').transport
          ⟨s, hs'⟩ ⟨t, ht'⟩ y) := by
  let q := max n m
  have hnq : n <= q := le_max_left _ _
  have hmq : m <= q := le_max_right _ _
  have hJq : Icc a b ⊆ (Q.flow q).time_domain :=
    fun _ ht => Q.stageTime n q hnq (hJ ht)
  have hKq : Icc c d ⊆ (Q.flow q).time_domain :=
    fun _ ht => Q.stageTime m q hmq (hK ht)
  have hfreeq := Q.stage_surgeryFreeTo n q hnq hJ hfree
  have hfreeq' := Q.stage_surgeryFreeTo m q hmq hK hfree'
  have hxyq : Q.stageIdentify n q hnq s (hJ hs) x =
      Q.stageIdentify m q hmq s (hK hs') y := by
    apply (Q.globalIdentify q s (hJq hs)).injective
    change Q.globalIdentify q s (hJq hs) (Q.stageIdentify n q hnq s (hJ hs) x) =
      Q.globalIdentify q s (hKq hs') (Q.stageIdentify m q hmq s (hK hs') y)
    rw [Q.globalIdentify_comp, Q.globalIdentify_comp]
    exact hxy
  have habq := ComposedExtension.ordinaryCompatibilityTo
    (Q.extensionBetween n q hnq) (Q.extensionBetween_eq n q hnq)
    a b hab hJ hfree hJq hfreeq ⟨s, hs⟩ ⟨t, ht⟩ x
  have hcdq := ComposedExtension.ordinaryCompatibilityTo
    (Q.extensionBetween m q hmq) (Q.extensionBetween_eq m q hmq)
    c d hcd hK hfree' hKq hfreeq' ⟨s, hs'⟩ ⟨t, ht'⟩ y
  calc
    _ = Q.globalIdentify q t (hJq ht)
        (Q.stageIdentify n q hnq t (hJ ht)
          (((Q.flow n).regular_slabs a b hab hJ hfree).transport
            ⟨s, hs⟩ ⟨t, ht⟩ x)) := (Q.globalIdentify_comp n q hnq t (hJ ht) _).symm
    _ = Q.globalIdentify q t (hJq ht)
        (((Q.flow q).regular_slabs a b hab hJq hfreeq).transport
          ⟨s, hs⟩ ⟨t, ht⟩ (Q.stageIdentify n q hnq s (hJ hs) x)) :=
      congrArg (Q.globalIdentify q t (hJq ht)) habq.symm
    _ = Q.globalIdentify q t (hKq ht')
        (((Q.flow q).regular_slabs c d hcd hKq hfreeq').transport
          ⟨s, hs'⟩ ⟨t, ht'⟩ (Q.stageIdentify n q hnq s (hJ hs) x)) := by
      congr 1
      exact (Q.flow q).slab_transport_coherent a b c d hab hJq hfreeq
        hcd hKq hfreeq' s t hs ht hs' ht' _
    _ = Q.globalIdentify q t (hKq ht')
        (((Q.flow q).regular_slabs c d hcd hKq hfreeq').transport
          ⟨s, hs'⟩ ⟨t, ht'⟩ (Q.stageIdentify m q hmq s (hK hs') y)) := by rw [hxyq]
    _ = Q.globalIdentify q t (hKq ht')
        (Q.stageIdentify m q hmq t (hK ht')
          (((Q.flow m).regular_slabs c d hcd hK hfree').transport
            ⟨s, hs'⟩ ⟨t, ht'⟩ y)) :=
      congrArg (Q.globalIdentify q t (hKq ht')) hcdq
    _ = _ := Q.globalIdentify_comp m q hmq t (hK ht') _

end PoincareConjecture.M51.CompletedStageChain
