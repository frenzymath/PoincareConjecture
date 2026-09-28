import PoincareConjecture.Proofs.M38.RegionEquivalences

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}

noncomputable def cylinderRegionHomeomorph (E : SurgeryRegionEquivalence A B U V) :
    U ≃ₜ V where
  toFun x := ⟨E.map x.val, E.map_image.subset ⟨x.val, x.property, rfl⟩⟩
  invFun y := ⟨E.inverse y.val, E.inverse_image.subset ⟨y.val, y.property, rfl⟩⟩
  left_inv x := Subtype.ext (E.left_inverse x.property)
  right_inv y := Subtype.ext (E.right_inverse y.property)
  continuous_toFun := E.map_smooth.continuousOn.domRestrict.subtype_mk _
  continuous_invFun := E.inverse_smooth.continuousOn.domRestrict.subtype_mk _

theorem cylinderCoordinate_mem (C : OpenCylinderModel V) {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) : C.coordinate z ∈ V := by
  have h := (C.homeomorph (z.1, ⟨z.2, hz.2⟩)).property
  rwa [C.coordinate_eq] at h

noncomputable def pullbackCylinder (E : SurgeryRegionEquivalence A B U V)
    (C : OpenCylinderModel V) : OpenCylinderModel U where
  homeomorph := C.homeomorph.trans (cylinderRegionHomeomorph E).symm
  coordinate := E.inverse ∘ C.coordinate
  coordinate_eq z := congrArg E.inverse (C.coordinate_eq z)
  coordinate_smooth := E.inverse_smooth.comp C.coordinate_smooth
    (fun _ hz => cylinderCoordinate_mem C hz)
  inverse := C.inverse ∘ E.map
  inverse_mem x hx := C.inverse_mem _ (E.map_image.subset ⟨x, hx, rfl⟩)
  left_inverse := by
    intro z hz
    change C.inverse (E.map (E.inverse (C.coordinate z))) = z
    rw [E.right_inverse (cylinderCoordinate_mem C hz), C.left_inverse hz]
  right_inverse := by
    intro x hx
    change E.inverse (C.coordinate (C.inverse (E.map x))) = x
    rw [C.right_inverse (E.map_image.subset ⟨x, hx, rfl⟩), E.left_inverse hx]
  inverse_smooth := C.inverse_smooth.comp E.map_smooth
    (fun x hx => E.map_image.subset ⟨x, hx, rfl⟩)

end PoincareConjecture.M38
