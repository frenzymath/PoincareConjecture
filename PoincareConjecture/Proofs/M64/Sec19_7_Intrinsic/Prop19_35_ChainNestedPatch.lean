import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ConcreteChainEndpoints
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NestedPatchContacts





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_chain_nested_patch_contacts
    {gamma : ℝ → AnnulusCoordinates} {a b : ℝ} {U C Z Z' : Set AnnulusCoordinates}
    (E : M64IntrinsicArcBandChain gamma a b U) (terminal : Bool) (hell : E.length ≤ 1)
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f : ℝ → ℝ} {a0 a1 ua wa ub wb ra rb sa sb : ℝ}
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a0 a1 ua wa ub wb ra rb)
    (B' : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a0 a1 ua wa ub wb sa sb)
    (hbase : L (if terminal then a1 else a0, f (if terminal then a1 else a0)) =
      gamma (if terminal then a else b))
    (hdirection : E.direction (if terminal then a else b) =
      (if terminal then rb else ra) • (if terminal then L (ub, wb) else L (ua, wa)))
    (hlength : (if terminal then sb else sa) = E.length * (if terminal then rb else ra))
    (hpath : ∀ z ∈ Icc (0 : ℝ) 1, gamma (if terminal then b else a) +
      z • E.direction (if terminal then b else a) ∈ C)
    (hBZ : B.carrier ∩ Z ⊆ if terminal then B.leftCut else B.rightCut)
    (hC : Disjoint C (B.carrier ∪ Z)) (hnew : B'.carrier ⊆ B.carrier) (hZ : Z' ⊆ Z)
    (hcutNew : (if terminal then B'.rightCut else B'.leftCut) ⊆
      if terminal then B.rightCut else B.leftCut)
    (hcontact : ∀ i, (C ∪ (B.carrier ∪ Z)) ∩ (E.band i).carrier =
      (if E.cut i.castSucc = a then (E.band i).leftCut else ∅) ∪
        (if E.cut i.succ = b then (E.band i).rightCut else ∅)) :
    (if terminal then B'.rightCut else B'.leftCut) =
      segment ℝ (gamma (if terminal then a else b))
        (gamma (if terminal then a else b) + E.length • E.direction (if terminal then a else b)) ∧
    ∀ i,
      C ∩ (E.band i).carrier =
        (if terminal then (if E.cut i.succ = b then (E.band i).rightCut else ∅)
          else (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)) ∧
      B'.carrier ∩ (E.band i).carrier =
        (if terminal then (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)
          else (if E.cut i.succ = b then (E.band i).rightCut else ∅)) ∧
      Disjoint Z' (E.band i).carrier := by
  have hcut : (if terminal then B'.rightCut else B'.leftCut) =
      segment ℝ (gamma (if terminal then a else b))
        (gamma (if terminal then a else b) +
          E.length • E.direction (if terminal then a else b)) := by
    cases terminal
    · change B'.leftCut = segment ℝ (gamma b) (gamma b + E.length • E.direction b)
      change L (a0, f a0) = gamma b at hbase
      change sa = E.length * ra at hlength
      change E.direction b = ra • L (ua, wa) at hdirection
      rw [m64Intrinsic_band_left_cut L B', hbase, hlength, hdirection, smul_smul]
    · change B'.rightCut = segment ℝ (gamma a) (gamma a + E.length • E.direction a)
      change L (a1, f a1) = gamma a at hbase
      change sb = E.length * rb at hlength
      change E.direction a = rb • L (ub, wb) at hdirection
      rw [m64Intrinsic_band_right_cut L B', hbase, hlength, hdirection, smul_smul]
  have hcapSegment : segment ℝ (gamma (if terminal then b else a))
      (gamma (if terminal then b else a) + E.length • E.direction (if terminal then b else a))
      ⊆ C := by
    rw [← m64Intrinsic_ray_image_eq_segment _ _ E.length_pos.le]
    rintro p ⟨z, hz, rfl⟩
    exact hpath z ⟨hz.1, hz.2.trans hell⟩
  have hcutCarrier : (if terminal then B'.rightCut else B'.leftCut) ⊆ B'.carrier := by
    rw [← B'.endpointEdge_image terminal]
    exact (B'.endpointEdge_subset_frontier terminal).trans B'.isClosed_carrier.frontier_subset
  refine ⟨hcut, ?_⟩
  intro i
  let S := if terminal then (if E.cut i.succ = b then (E.band i).rightCut else ∅)
    else (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)
  let T := if terminal then (if E.cut i.castSucc = a then (E.band i).leftCut else ∅)
    else (if E.cut i.succ = b then (E.band i).rightCut else ∅)
  have hS : S ⊆ C := by
    intro p hp
    cases terminal
    · change p ∈ (if E.cut i.castSucc = a then (E.band i).leftCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.left_cut, he] at hp
        exact hcapSegment hp
      · exact hp.elim
    · change p ∈ (if E.cut i.succ = b then (E.band i).rightCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.right_cut, he] at hp
        exact hcapSegment hp
      · exact hp.elim
  have hTcut : T ⊆ (if terminal then B'.rightCut else B'.leftCut) := by
    intro p hp
    rw [hcut]
    cases terminal
    · change p ∈ (if E.cut i.succ = b then (E.band i).rightCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.right_cut, he] at hp
        exact hp
      · exact hp.elim
    · change p ∈ (if E.cut i.castSucc = a then (E.band i).leftCut else ∅) at hp
      split_ifs at hp with he
      · rw [E.left_cut, he] at hp
        exact hp
      · exact hp.elim
  have hT : T ⊆ (if terminal then B.rightCut else B.leftCut) ∩ B'.carrier :=
    subset_inter (hTcut.trans hcutNew) (hTcut.trans hcutCarrier)
  have hcontact' : (C ∪ (B.carrier ∪ Z)) ∩ (E.band i).carrier = S ∪ T := by
    rw [hcontact]
    cases terminal
    · rfl
    · exact union_comm _ _
  exact m64Intrinsic_nested_patch_obstacle_contacts B terminal hBZ hC hnew hZ hS hT hcontact'

end PoincareConjecture
