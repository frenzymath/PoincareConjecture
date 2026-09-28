import PoincareConjecture.Proofs.M38.UnionRefinement
import PoincareConjecture.Proofs.M38.BallRegionTransport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38


def sumFullRegion {A : GeneralizedSliceCarrier.{u}} (D : GeneralizedSliceCarrier.{u})
    (U : Set A.carrier) : Set (sumCarrier A D).carrier :=
  Sum.inl '' U ∪ Set.range Sum.inr


theorem sumMapId_contMDiffOn {A B : GeneralizedSliceCarrier.{u}}
    (D : GeneralizedSliceCarrier.{u}) {U : Set A.carrier} (hU : IsOpen U)
    {f : A.carrier → B.carrier} (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Sum.map f id :
      (sumCarrier A D).carrier → (sumCarrier B D).carrier) (sumFullRegion D U) := by
  intro q hq
  cases q with
  | inl x =>
      have hx : x ∈ U := by simpa [sumFullRegion] using hq
      let r : (sumCarrier A D).carrier → A.carrier := Sum.elim id (fun _ => x)
      have hr : ContMDiff (𝓡 3) (𝓡 3) ∞ r :=
        ContMDiff.sumElim contMDiff_id contMDiff_const
      have hf' : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (r (Sum.inl x)) :=
        hf.contMDiffAt (hU.mem_nhds hx)
      have hlocal : ContMDiffAt (𝓡 3) (𝓡 3) ∞
          (fun q => (Sum.inl (f (r q)) : (sumCarrier B D).carrier)) (Sum.inl x) :=
        ContMDiff.inl.contMDiffAt.comp _ (hf'.comp _ (hr _))
      apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [isOpen_range_inl.mem_nhds (Set.mem_range_self x)] with q hq
      obtain ⟨y, rfl⟩ := hq
      rfl
  | inr x =>
      let r : (sumCarrier A D).carrier → D.carrier := Sum.elim (fun _ => x) id
      have hr : ContMDiff (𝓡 3) (𝓡 3) ∞ r :=
        ContMDiff.sumElim contMDiff_const contMDiff_id
      have hlocal : ContMDiffAt (𝓡 3) (𝓡 3) ∞
          (fun q => (Sum.inr (r q) : (sumCarrier B D).carrier)) (Sum.inr x) :=
        ContMDiff.inr.contMDiffAt.comp _ (hr _)
      apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [isOpen_range_inr.mem_nhds (Set.mem_range_self x)] with q hq
      obtain ⟨y, rfl⟩ := hq
      rfl


def sumRegionEquivalence {A B : GeneralizedSliceCarrier.{u}}
    (D : GeneralizedSliceCarrier.{u}) {U : Set A.carrier} {V : Set B.carrier}
    (E : SurgeryRegionEquivalence A B U V) (hU : IsOpen U) (hV : IsOpen V) :
    SurgeryRegionEquivalence (sumCarrier A D) (sumCarrier B D)
      (sumFullRegion D U) (sumFullRegion D V) where
  map := Sum.map E.map id
  inverse := Sum.map E.inverse id
  map_image := by
    apply Set.Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      rcases hq with ⟨x, hx, rfl⟩ | ⟨x, rfl⟩
      · exact Or.inl ⟨E.map x, E.map_image.subset ⟨x, hx, rfl⟩, rfl⟩
      · exact Or.inr (Set.mem_range_self x)
    · rintro _ (⟨x, hx, rfl⟩ | ⟨x, rfl⟩)
      · obtain ⟨a, ha, rfl⟩ := E.map_image.symm ▸ hx
        exact ⟨Sum.inl a, Or.inl ⟨a, ha, rfl⟩, rfl⟩
      · exact ⟨Sum.inr x, Or.inr (Set.mem_range_self x), rfl⟩
  inverse_image := by
    apply Set.Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      rcases hq with ⟨x, hx, rfl⟩ | ⟨x, rfl⟩
      · exact Or.inl ⟨E.inverse x, E.inverse_image.subset ⟨x, hx, rfl⟩, rfl⟩
      · exact Or.inr (Set.mem_range_self x)
    · rintro _ (⟨x, hx, rfl⟩ | ⟨x, rfl⟩)
      · obtain ⟨a, ha, rfl⟩ := E.inverse_image.symm ▸ hx
        exact ⟨Sum.inl a, Or.inl ⟨a, ha, rfl⟩, rfl⟩
      · exact ⟨Sum.inr x, Or.inr (Set.mem_range_self x), rfl⟩
  left_inverse := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, rfl⟩)
    · exact congrArg Sum.inl (E.left_inverse hx)
    · rfl
  right_inverse := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨x, rfl⟩)
    · exact congrArg Sum.inl (E.right_inverse hx)
    · rfl
  map_smooth := sumMapId_contMDiffOn D hU E.map_smooth
  inverse_smooth := sumMapId_contMDiffOn D hV E.inverse_smooth


theorem sumFullRegion_open {A : GeneralizedSliceCarrier.{u}}
    (D : GeneralizedSliceCarrier.{u}) {U : Set A.carrier} (hU : IsOpen U) :
    IsOpen (sumFullRegion D U) :=
  (isOpenMap_inl _ hU).union isOpen_range_inr


theorem sumFullRegion_closed {A : GeneralizedSliceCarrier.{u}}
    (D : GeneralizedSliceCarrier.{u}) {U : Set A.carrier} (hU : IsClosed U) :
    IsClosed (sumFullRegion D U) :=
  (isClosedMap_inl _ hU).union isClosed_range_inr


theorem sumFullRegion_disjoint_inl {A : GeneralizedSliceCarrier.{u}}
    (D : GeneralizedSliceCarrier.{u}) {U V : Set A.carrier} (h : Disjoint U V) :
    Disjoint (sumFullRegion D U) (Sum.inl '' V) := by
  apply Set.disjoint_left.mpr
  rintro _ (hx | ⟨d, hd⟩) ⟨v, hv, rfl⟩
  · obtain ⟨a, ha, hav⟩ := hx
    exact Set.disjoint_left.mp h ha ((Sum.inl_injective hav).symm ▸ hv)
  · cases hd


noncomputable def sumInlBall {A : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A) (D : GeneralizedSliceCarrier.{u}) :
    SurgeryBallEmbedding (sumCarrier A D) :=
  transportSurgeryBallRegion B (sumInlEquivalence A D ⟨B.map 0⟩)
    isOpen_univ isOpen_range_inl (Set.subset_univ _)


theorem sumInlBall_map {A : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A) (D : GeneralizedSliceCarrier.{u}) (x : StandardCapSpace) :
    (sumInlBall B D).map x = Sum.inl (B.map x) := rfl


theorem sumInlBall_closedBall {A : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A) (D : GeneralizedSliceCarrier.{u}) :
    (sumInlBall B D).closedBall = Sum.inl '' B.closedBall := by
  exact transportSurgeryBallRegion_closedBall B
    (sumInlEquivalence A D ⟨B.map 0⟩) isOpen_univ isOpen_range_inl (Set.subset_univ _)


theorem sumInlBall_complement {A : GeneralizedSliceCarrier.{u}}
    (B : SurgeryBallEmbedding A) (D : GeneralizedSliceCarrier.{u}) :
    (sumInlBall B D).closedBallᶜ = sumFullRegion D B.closedBallᶜ := by
  rw [sumInlBall_closedBall]
  ext q
  cases q with
  | inl x =>
      constructor
      · intro hx
        exact Or.inl ⟨x, fun h => hx ⟨x, h, rfl⟩, rfl⟩
      · rintro (⟨y, hy, heq⟩ | ⟨y, heq⟩) ⟨z, hz, hzx⟩
        · have hyx : y = x := Sum.inl_injective heq
          have hzx' : z = x := Sum.inl_injective hzx
          exact hy (hyx.symm ▸ hzx' ▸ hz)
        · cases heq
  | inr x =>
      constructor
      · intro _
        exact Or.inr (Set.mem_range_self x)
      · rintro _ ⟨z, _, heq⟩
        cases heq

end PoincareConjecture.M38
