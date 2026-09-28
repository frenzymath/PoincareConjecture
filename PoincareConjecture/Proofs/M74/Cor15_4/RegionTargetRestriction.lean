import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.Carriers.Opens
import PoincareConjecture.Proofs.M74.Mathlib.OpenTargetLift










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryRegionEquivalence

variable {A C : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set C.carrier}
  (E : SurgeryRegionEquivalence A C U V) (T : TopologicalSpace.Opens C.carrier)
  (hVT : V ⊆ T) (y0 : T)



noncomputable def restrictOpenTargetOn :
    SurgeryRegionEquivalence A (C.opens T) U (Subtype.val ⁻¹' V) where
  map := T.liftMap y0 E.map
  inverse := E.inverse ∘ Subtype.val
  map_image := by
    change (T.liftMap y0 E.map '' U : Set T) = Subtype.val ⁻¹' V
    rw [T.liftMap_image y0 E.map (fun _ hx => hVT
      (E.map_image.subset (mem_image_of_mem _ hx))), E.map_image]
  inverse_image := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact E.inverse_image.subset (mem_image_of_mem _ hy)
    · intro hx
      have hmap := E.map_image.subset (mem_image_of_mem _ hx)
      exact ⟨⟨E.map x, hVT hmap⟩, hmap, E.left_inverse hx⟩
  left_inverse := by
    intro x hx
    change E.inverse (T.liftMap y0 E.map x).val = x
    rw [T.liftMap_val_of_mem y0 E.map (hVT
      (E.map_image.subset (mem_image_of_mem _ hx)))]
    exact E.left_inverse hx
  right_inverse := by
    intro y hy
    apply Subtype.ext
    change (T.liftMap y0 E.map (E.inverse y.val)).val = y.val
    rw [T.liftMap_val_of_mem y0 E.map (by
      rw [E.right_inverse hy]
      exact y.property), E.right_inverse hy]
  map_smooth := T.contMDiffOn_liftMap y0 E.map_smooth
    (fun _ hx => hVT (E.map_image.subset (mem_image_of_mem _ hx)))
  inverse_smooth := E.inverse_smooth.comp contMDiff_subtype_val.contMDiffOn
    (fun _ hx => hx)



theorem restrictOpenTargetOn_map_val {x : A.carrier} (hx : x ∈ U) :
    ((E.restrictOpenTargetOn T hVT y0).map x).val = E.map x :=
  T.liftMap_val_of_mem y0 E.map (hVT (E.map_image.subset (mem_image_of_mem _ hx)))



theorem restrictOpenTargetOn_inverse (x : (C.opens T).carrier) :
    (E.restrictOpenTargetOn T hVT y0).inverse x = E.inverse x.val := rfl

end PoincareConjecture.SurgeryRegionEquivalence

namespace PoincareConjecture.GeneralizedSliceCarrier




noncomputable def opensEquivalence (C : GeneralizedSliceCarrier.{u})
    (T : TopologicalSpace.Opens C.carrier) (y0 : T) :
    SurgeryRegionEquivalence (C.opens T) C univ T where
  map := Subtype.val
  inverse := T.liftMap y0 id
  map_image := by
    change Subtype.val '' (univ : Set T) = (T : Set C.carrier)
    ext x
    simp
  inverse_image := by
    apply Subset.antisymm (subset_univ _)
    intro x _
    exact ⟨x.val, x.property, Subtype.ext (T.liftMap_val_of_mem y0 id x.property)⟩
  left_inverse := by
    intro x _
    exact Subtype.ext (T.liftMap_val_of_mem y0 id x.property)
  right_inverse := fun _ hx => T.liftMap_val_of_mem y0 id hx
  map_smooth := (C.opens_val_smooth T).contMDiffOn
  inverse_smooth := T.contMDiffOn_liftMap y0 contMDiff_id.contMDiffOn (mapsTo_id _)

end PoincareConjecture.GeneralizedSliceCarrier
