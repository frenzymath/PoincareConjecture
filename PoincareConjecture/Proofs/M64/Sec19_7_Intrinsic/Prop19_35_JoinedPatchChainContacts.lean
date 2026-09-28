import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_JoinedPatchData
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChainNestedPatch





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_joined_patch_chain_contacts
    {gamma : Bool → ℝ → AnnulusCoordinates} {T b : Bool → ℝ}
    {U C : Set AnnulusCoordinates} (P Q : M64IntrinsicJoinedBandPatch gamma T b U)
    (e : Bool) {a d : ℝ} (E : M64IntrinsicArcBandChain (gamma e) a d U)
    (hell : E.length ≤ 1) (hattach : b e = if e then a else d)
    (hdir : E.direction (if e then a else d) =
      (if e then P.right_length else P.left_length) • P.direction)
    (hQdir : Q.direction = P.direction)
    (hQlength : (if e then Q.right_length else Q.left_length) =
      E.length * (if e then P.right_length else P.left_length))
    (hpath : ∀ z ∈ Icc (0 : ℝ) 1, gamma e (if e then d else a) +
      z • E.direction (if e then d else a) ∈ C)
    (hC : Disjoint C ((P.band e).carrier ∪ (P.band (!e)).carrier))
    (hnew : ∀ j, (Q.band j).carrier ⊆ (P.band j).carrier)
    (houter : (Q.band e).carrier ∩
      (if e then (P.band e).rightCut else (P.band e).leftCut) =
        (if e then (Q.band e).rightCut else (Q.band e).leftCut))
    (hcontact : ∀ i, (C ∪ ((P.band e).carrier ∪ (P.band (!e)).carrier)) ∩
      (E.band i).carrier = (if E.cut i.castSucc = a then (E.band i).leftCut else ∅) ∪
        (if E.cut i.succ = d then (E.band i).rightCut else ∅)) :
    (if e then (Q.band e).rightCut else (Q.band e).leftCut) =
      segment ℝ (gamma e (if e then a else d))
        (gamma e (if e then a else d) + E.length • E.direction (if e then a else d)) ∧
    ∀ i,
      C ∩ (E.band i).carrier =
        (if e then (if E.cut i.succ = d then (E.band i).rightCut else ∅)
          else (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)) ∧
      (Q.band e).carrier ∩ (E.band i).carrier =
        (if e then (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)
          else (if E.cut i.succ = d then (E.band i).rightCut else ∅)) ∧
      Disjoint (Q.band (!e)).carrier (E.band i).carrier := by
  have hcut : (if e then (Q.band e).rightCut else (Q.band e).leftCut) =
      segment ℝ (gamma e (if e then a else d))
        (gamma e (if e then a else d) + E.length • E.direction (if e then a else d)) := by
    rw [Q.outer_cut, hattach, hQdir, hQlength, hdir, smul_smul]
  have hBZ : (P.band e).carrier ∩ (P.band (!e)).carrier ⊆
      if e then (P.band e).leftCut else (P.band e).rightCut := by
    cases e
    · exact (P.intersection.trans (P.inner_cut false).symm).subset
    · exact ((inter_comm _ _).trans (P.intersection.trans (P.inner_cut true).symm)).subset
  have hnewCut : (if e then (Q.band e).rightCut else (Q.band e).leftCut) ⊆
      if e then (P.band e).rightCut else (P.band e).leftCut :=
    fun _ hp => (houter.symm.subset hp).2
  have hcutCarrier : (if e then (Q.band e).rightCut else (Q.band e).leftCut) ⊆
      (Q.band e).carrier := by
    rw [← (Q.band e).endpointEdge_image e]
    exact ((Q.band e).endpointEdge_subset_frontier e).trans
      (Q.band e).isClosed_carrier.frontier_subset
  have hcapSegment : segment ℝ (gamma e (if e then d else a))
      (gamma e (if e then d else a) + E.length • E.direction (if e then d else a)) ⊆ C := by
    rw [← m64Intrinsic_ray_image_eq_segment _ _ E.length_pos.le]
    rintro p ⟨z, hz, rfl⟩
    exact hpath z ⟨hz.1, hz.2.trans hell⟩
  refine ⟨hcut, ?_⟩
  intro i
  let S := if e then (if E.cut i.succ = d then (E.band i).rightCut else ∅)
    else (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)
  let R := if e then (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)
    else (if E.cut i.succ = d then (E.band i).rightCut else ∅)
  have hS : S ⊆ C := by
    intro p hp
    cases e
    · change p ∈ (if E.cut i.castSucc = a then (E.band i).leftCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.left_cut, he] at hp
        exact hcapSegment hp
      · exact hp.elim
    · change p ∈ (if E.cut i.succ = d then (E.band i).rightCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.right_cut, he] at hp
        exact hcapSegment hp
      · exact hp.elim
  have hRcut : R ⊆ (if e then (Q.band e).rightCut else (Q.band e).leftCut) := by
    intro p hp
    rw [hcut]
    cases e
    · change p ∈ (if E.cut i.succ = d then (E.band i).rightCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.right_cut, he] at hp
        exact hp
      · exact hp.elim
    · change p ∈ (if E.cut i.castSucc = a then (E.band i).leftCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.left_cut, he] at hp
        exact hp
      · exact hp.elim
  have hR : R ⊆ (if e then (P.band e).rightCut else (P.band e).leftCut) ∩
      (Q.band e).carrier := subset_inter (hRcut.trans hnewCut) (hRcut.trans hcutCarrier)
  have hcontact' : (C ∪ ((P.band e).carrier ∪ (P.band (!e)).carrier)) ∩
      (E.band i).carrier = S ∪ R := by
    rw [hcontact]
    cases e
    · rfl
    · exact union_comm _ _
  exact m64Intrinsic_nested_patch_obstacle_contacts (P.band e) e hBZ hC
    (hnew e) (hnew (!e)) hS hR hcontact'

end PoincareConjecture
