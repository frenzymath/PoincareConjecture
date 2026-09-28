import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.Separation.Regular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Topology

universe u

namespace PoincareConjecture

variable {P Q : GeneralizedSliceCarrier.{u}}



noncomputable abbrev GeneralizedSliceCarrier.sum (P Q : GeneralizedSliceCarrier.{u}) :
    GeneralizedSliceCarrier.{u} where
  carrier := P.carrier ⊕ Q.carrier
  topologicalSpace := inferInstance
  measurableSpace := borel (P.carrier ⊕ Q.carrier)
  borelSpace := @BorelSpace.mk _ inferInstance (borel _) rfl
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := {
    toT0Space := inferInstance
    toRegularSpace := RegularSpace.of_exists_mem_nhds_isClosed_subset (fun x s hs => by
      cases x with
      | inl x =>
          have hs' : (Sum.inl ⁻¹' s : Set P.carrier) ∈ 𝓝 x :=
            continuous_inl.continuousAt.preimage_mem_nhds hs
          obtain ⟨t, ht, htc, hts⟩ :=
            exists_mem_nhds_isClosed_subset hs'
          refine ⟨Sum.inl '' t, ?_, IsClosedEmbedding.inl.isClosed_iff_image_isClosed.mp htc, ?_⟩
          · exact IsOpenEmbedding.inl.image_mem_nhds.mpr ht
          · exact Set.image_subset_iff.mpr hts
      | inr x =>
          have hs' : (Sum.inr ⁻¹' s : Set Q.carrier) ∈ 𝓝 x :=
            continuous_inr.continuousAt.preimage_mem_nhds hs
          obtain ⟨t, ht, htc, hts⟩ :=
            exists_mem_nhds_isClosed_subset hs'
          refine ⟨Sum.inr '' t, ?_, IsClosedEmbedding.inr.isClosed_iff_image_isClosed.mp htc, ?_⟩
          · exact IsOpenEmbedding.inr.image_mem_nhds.mpr ht
          · exact Set.image_subset_iff.mpr hts
      ) }
  secondCountable := inferInstance


theorem GeneralizedSliceCarrier.sum_inl_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (Sum.inl : P.carrier → (P.sum Q).carrier) :=
  ContMDiff.inl


theorem GeneralizedSliceCarrier.sum_inr_smooth :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (Sum.inr : Q.carrier → (P.sum Q).carrier) :=
  ContMDiff.inr


theorem GeneralizedSliceCarrier.sum_inl_clopen :
    IsClopen (Set.range (Sum.inl : P.carrier → (P.sum Q).carrier)) :=
  ⟨isClosed_range_inl, isOpen_range_inl⟩


theorem GeneralizedSliceCarrier.sum_inr_clopen :
    IsClopen (Set.range (Sum.inr : Q.carrier → (P.sum Q).carrier)) :=
  ⟨isClosed_range_inr, isOpen_range_inr⟩

section SmoothOn

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]



theorem m72ContMDiffOn_sumElim_inl {f : P.carrier → X} (g : Q.carrier → X)
    {U : Set P.carrier} (hf : ContMDiffOn (𝓡 3) J ∞ f U) :
    ContMDiffOn (𝓡 3) J ∞ (Sum.elim f g : (P.sum Q).carrier → X) (Sum.inl '' U) := by
  rintro _ ⟨x, hx, rfl⟩
  let r : (P.sum Q).carrier → P.carrier := Sum.elim id (fun _ => x)
  have hr : ContMDiff (𝓡 3) (𝓡 3) ∞ r :=
    contMDiff_id.sumElim contMDiff_const
  have hfr : ContMDiffOn (𝓡 3) J ∞ (f ∘ r) (Sum.inl '' U) :=
    hf.comp hr.contMDiffOn (by rintro _ ⟨y, hy, rfl⟩; exact hy)
  apply (hfr (Sum.inl x) (Set.mem_image_of_mem _ hx)).congr
  · rintro _ ⟨y, _, rfl⟩
    rfl
  · rfl



theorem m72ContMDiffOn_sumElim_inr (f : P.carrier → X) {g : Q.carrier → X}
    {U : Set Q.carrier} (hg : ContMDiffOn (𝓡 3) J ∞ g U) :
    ContMDiffOn (𝓡 3) J ∞ (Sum.elim f g : (P.sum Q).carrier → X) (Sum.inr '' U) := by
  rintro _ ⟨x, hx, rfl⟩
  let r : (P.sum Q).carrier → Q.carrier := Sum.elim (fun _ => x) id
  have hr : ContMDiff (𝓡 3) (𝓡 3) ∞ r :=
    contMDiff_const.sumElim contMDiff_id
  have hgr : ContMDiffOn (𝓡 3) J ∞ (g ∘ r) (Sum.inr '' U) :=
    hg.comp hr.contMDiffOn (by rintro _ ⟨y, hy, rfl⟩; exact hy)
  apply (hgr (Sum.inr x) (Set.mem_image_of_mem _ hx)).congr
  · rintro _ ⟨y, _, rfl⟩
    rfl
  · rfl



theorem m72ContMDiffOn_sumElim {f : P.carrier → X} {g : Q.carrier → X}
    {U : Set P.carrier} {V : Set Q.carrier}
    (hf : ContMDiffOn (𝓡 3) J ∞ f U) (hg : ContMDiffOn (𝓡 3) J ∞ g V)
    (hU : IsOpen U) (hV : IsOpen V) :
    ContMDiffOn (𝓡 3) J ∞ (Sum.elim f g : (P.sum Q).carrier → X)
      ((Sum.inl '' U) ∪ (Sum.inr '' V)) :=
  (m72ContMDiffOn_sumElim_inl g hf).union_of_isOpen
    (m72ContMDiffOn_sumElim_inr f hg) (isOpenMap_inl U hU) (isOpenMap_inr V hV)

end SmoothOn

namespace SurgeryRegionEquivalence

variable {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}



noncomputable def sumInl (E : SurgeryRegionEquivalence A B U V)
    (Z : GeneralizedSliceCarrier.{u}) (a : A.carrier) :
    SurgeryRegionEquivalence A (B.sum Z) U (Sum.inl '' V) where
  map := Sum.inl ∘ E.map
  inverse := Sum.elim E.inverse (fun _ => a)
  map_image := by rw [Set.image_comp, E.map_image]
  inverse_image := by
    rw [Set.image_image]
    exact E.inverse_image
  left_inverse := by
    intro x hx
    exact E.left_inverse hx
  right_inverse := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Sum.inl (E.right_inverse hx)
  map_smooth := ContMDiff.inl.comp_contMDiffOn E.map_smooth
  inverse_smooth := m72ContMDiffOn_sumElim_inl _ E.inverse_smooth



noncomputable def sumInr (E : SurgeryRegionEquivalence A B U V)
    (Z : GeneralizedSliceCarrier.{u}) (a : A.carrier) :
    SurgeryRegionEquivalence A (Z.sum B) U (Sum.inr '' V) where
  map := Sum.inr ∘ E.map
  inverse := Sum.elim (fun _ => a) E.inverse
  map_image := by rw [Set.image_comp, E.map_image]
  inverse_image := by
    rw [Set.image_image]
    exact E.inverse_image
  left_inverse := by
    intro x hx
    exact E.left_inverse hx
  right_inverse := by
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Sum.inr (E.right_inverse hx)
  map_smooth := ContMDiff.inr.comp_contMDiffOn E.map_smooth
  inverse_smooth := m72ContMDiffOn_sumElim_inr _ E.inverse_smooth

end SurgeryRegionEquivalence



noncomputable def SurgeryRegionEquivalence.sumRight
    {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}
    (E : SurgeryRegionEquivalence A B U V) (Z : GeneralizedSliceCarrier.{u})
    (hU : IsOpen U) (hV : IsOpen V) :
    SurgeryRegionEquivalence (A.sum Z) (B.sum Z)
      ((Sum.inl '' U) ∪ Set.range Sum.inr)
      ((Sum.inl '' V) ∪ Set.range Sum.inr) where
  map := Sum.elim (Sum.inl ∘ E.map) Sum.inr
  inverse := Sum.elim (Sum.inl ∘ E.inverse) Sum.inr
  map_image := by
    ext x
    cases x <;> simp [← E.map_image, Set.mem_image, Set.mem_range]
  inverse_image := by
    ext x
    cases x <;> simp [← E.inverse_image, Set.mem_image, Set.mem_range]
  left_inverse := by
    rintro x (hx | hx)
    · rcases hx with ⟨y, hy, rfl⟩
      exact congrArg Sum.inl (E.left_inverse hy)
    · rcases hx with ⟨y, rfl⟩
      rfl
  right_inverse := by
    rintro x (hx | hx)
    · rcases hx with ⟨y, hy, rfl⟩
      exact congrArg Sum.inl (E.right_inverse hy)
    · rcases hx with ⟨y, rfl⟩
      rfl
  map_smooth := by
    simpa only [Set.image_univ] using
      m72ContMDiffOn_sumElim
        (ContMDiff.inl.comp_contMDiffOn E.map_smooth)
        (ContMDiff.inr.contMDiffOn (s := Set.univ)) hU isOpen_univ
  inverse_smooth := by
    simpa only [Set.image_univ] using
      m72ContMDiffOn_sumElim
        (ContMDiff.inl.comp_contMDiffOn E.inverse_smooth)
        (ContMDiff.inr.contMDiffOn (s := Set.univ)) hV isOpen_univ

end PoincareConjecture
