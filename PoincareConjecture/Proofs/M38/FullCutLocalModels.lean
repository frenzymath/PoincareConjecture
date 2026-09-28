import PoincareConjecture.Proofs.M38.Components
import PoincareConjecture.Proofs.M38.CapPatch
import PoincareConjecture.Proofs.M38.OneCapAssembly
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

noncomputable def regionPartialDiffeomorph
    {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}
    (E : SurgeryRegionEquivalence A B U V) (hU : IsOpen U) (hV : IsOpen V) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞ where
  toFun := E.map
  invFun := E.inverse
  source := U
  target := V
  map_source' := fun x hx => E.map_image.subset (Set.mem_image_of_mem _ hx)
  map_target' := fun y hy => E.inverse_image.subset (Set.mem_image_of_mem _ hy)
  left_inv' := E.left_inverse
  right_inv' := E.right_inverse
  open_source := hU
  open_target := hV
  contMDiffOn_toFun := E.map_smooth
  contMDiffOn_invFun := E.inverse_smooth

theorem openSubtype_localDiffeomorph (A : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens A.carrier) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (Subtype.val : U → A.carrier) := by
  intro x
  let d := regionPartialDiffeomorph (openRegionEquivalence A U x) isOpen_univ U.isOpen
  exact ⟨d, Set.mem_univ x, fun _ _ => rfl⟩

theorem openInclusion_localDiffeomorph (A : GeneralizedSliceCarrier.{u})
    (U V : TopologicalSpace.Opens A.carrier) (hUV : U ≤ V) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (TopologicalSpace.Opens.inclusion hUV) := by
  intro x
  let eU := openRegionEquivalence A U x
  let eV := openRegionEquivalence A V (Set.inclusion hUV x)
  let dU := regionPartialDiffeomorph eU isOpen_univ U.isOpen
  let dV := regionPartialDiffeomorph eV isOpen_univ V.isOpen
  refine ⟨dU.trans dV.symm, ⟨Set.mem_univ x, hUV x.property⟩, ?_⟩
  intro y _
  apply Subtype.ext
  exact (eV.right_inverse (hUV y.property)).symm

noncomputable def surgeryBallPartialDiffeomorph (A : GeneralizedSliceCarrier.{u})
    (B : SurgeryBallEmbedding A) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace A.carrier ∞ where
  toFun := B.map
  invFun := B.inverse
  source := Metric.ball 0 2
  target := B.map '' Metric.ball 0 2
  map_source' := fun x hx => Set.mem_image_of_mem _ hx
  map_target' := by
    rintro y ⟨x, hx, rfl⟩
    rwa [B.left_inverse hx]
  left_inv' := B.left_inverse
  right_inv' := B.right_inverse
  open_source := Metric.isOpen_ball
  open_target := by
    have h := B.open_embedding.isOpen_range
    change IsOpen (Set.range (B.map ∘
      (Subtype.val : Metric.ball (0 : StandardCapSpace) 2 → StandardCapSpace))) at h
    simpa only [Set.range_comp, Subtype.range_coe_subtype, Set.ofPred_mem_eq] using h
  contMDiffOn_toFun := B.map_smooth
  contMDiffOn_invFun := B.inverse_smooth

theorem surgeryBall_map_localDiffeomorph (A : GeneralizedSliceCarrier.{u})
    (B : SurgeryBallEmbedding A) {x : StandardCapSpace} (hx : x ∈ Metric.ball 0 2) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ B.map x :=
  ⟨surgeryBallPartialDiffeomorph A B, hx, fun _ _ => rfl⟩

theorem surgeryBall_patch_localDiffeomorph (A : GeneralizedSliceCarrier.{u})
    (B : SurgeryBallEmbedding A) :
    letI : Nonempty capDoubleBall := capDoubleBall_nonempty
    letI := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : capDoubleBall => B.map x.val) := by
  letI : Nonempty capDoubleBall := capDoubleBall_nonempty
  letI := capDoubleBall.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro x
  exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3)
    (capDoubleBall : Set StandardCapSpace) capDoubleBall.isOpen ∞ x).comp (𝓡 3) A.carrier
      (surgeryBall_map_localDiffeomorph A B x.property)

theorem sumInl_localDiffeomorph (A B : GeneralizedSliceCarrier.{u}) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Sum.inl : A.carrier → (sumCarrier A B).carrier) := by
  intro x
  let d := regionPartialDiffeomorph (sumInlEquivalence A B ⟨x⟩)
    isOpen_univ isOpen_range_inl
  exact ⟨d, Set.mem_univ x, fun _ _ => rfl⟩

theorem sumInr_localDiffeomorph (A B : GeneralizedSliceCarrier.{u}) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Sum.inr : B.carrier → (sumCarrier A B).carrier) := by
  intro x
  let d := regionPartialDiffeomorph (sumInrEquivalence A B ⟨x⟩)
    isOpen_univ isOpen_range_inr
  exact ⟨d, Set.mem_univ x, fun _ _ => rfl⟩

end PoincareConjecture.M38
