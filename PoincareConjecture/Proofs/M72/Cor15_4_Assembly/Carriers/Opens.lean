import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import Mathlib.Topology.Connected.LocallyConnected









set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



noncomputable def GeneralizedSliceCarrier.opens (A : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens A.carrier) : GeneralizedSliceCarrier.{u} where
  carrier := U
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance



theorem GeneralizedSliceCarrier.opens_val_smooth (A : GeneralizedSliceCarrier.{u})
    (U : TopologicalSpace.Opens A.carrier) :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : (A.opens U).carrier => x.val) :=
  contMDiff_subtype_val



instance GeneralizedSliceCarrier.locallyConnectedSpace (A : GeneralizedSliceCarrier.{u}) :
    LocallyConnectedSpace A.carrier :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) A.carrier



noncomputable def SurgeryRegionEquivalence.restrictOpenTarget
    {A B : GeneralizedSliceCarrier.{u}} {V : Set B.carrier}
    (E : SurgeryRegionEquivalence A B Set.univ V)
    (U : TopologicalSpace.Opens B.carrier) (hVU : V ⊆ U) :
    SurgeryRegionEquivalence A (B.opens U) Set.univ (Subtype.val ⁻¹' V) where
  map := fun x => ⟨E.map x, hVU (E.map_image.subset
    (Set.mem_image_of_mem _ (Set.mem_univ x)))⟩
  inverse := fun x => E.inverse x.val
  map_image := by
    ext y
    constructor
    · rintro ⟨x, _, rfl⟩
      exact E.map_image.subset (Set.mem_image_of_mem _ (Set.mem_univ x))
    · intro hy
      obtain ⟨x, hx, heq⟩ := E.map_image.symm.subset hy
      exact ⟨x, hx, Subtype.ext heq⟩
  inverse_image := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x hx
    refine ⟨⟨E.map x, hVU (E.map_image.subset (Set.mem_image_of_mem _ hx))⟩,
      E.map_image.subset (Set.mem_image_of_mem _ hx), E.left_inverse hx⟩
  left_inverse := E.left_inverse
  right_inverse := by
    intro x hx
    exact Subtype.ext (E.right_inverse hx)
  map_smooth := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ Set.univ x).mp
    exact E.map_smooth x hx
  inverse_smooth := E.inverse_smooth.comp contMDiff_subtype_val.contMDiffOn
    (fun _ hx => hx)

end PoincareConjecture
