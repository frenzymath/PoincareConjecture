import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem m57Component_inverse_right
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    {x : A.carrier} (hx : x ∈ range C.inclusion) : C.inclusion (C.inverse x) = x := by
  obtain ⟨y, rfl⟩ := hx
  exact congrArg C.inclusion (C.left_inverse y)

theorem m57RegionInverse_localDiffeomorph
    {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}
    (e : SurgeryRegionEquivalence A B U V) (hU : IsOpen U) (hV : IsOpen V)
    (y : B.carrier) (hy : y ∈ V) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ e.inverse y := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) B.carrier A.carrier ∞ :=
    { toFun := e.inverse
      invFun := e.map
      source := V
      target := U
      map_source' := by
        intro x hx
        exact e.inverse_image.subset ⟨x, hx, rfl⟩
      map_target' := by
        intro x hx
        exact e.map_image.subset ⟨x, hx, rfl⟩
      left_inv' := e.right_inverse
      right_inv' := e.left_inverse
      open_source := hV
      open_target := hU
      contMDiffOn_toFun := e.inverse_smooth
      contMDiffOn_invFun := e.map_smooth }
  exact ⟨d, hy, fun _ _ => rfl⟩

theorem m57ComponentInverse_localDiffeomorph
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (x : A.carrier) (hx : x ∈ range C.inclusion) :
    IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ C.inverse x := by
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) A.carrier C.carrier.carrier ∞ :=
    { toFun := C.inverse
      invFun := C.inclusion
      source := range C.inclusion
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun y _ => ⟨y, rfl⟩
      left_inv' := fun _ hy => m57Component_inverse_right C hy
      right_inv' := fun y _ => C.left_inverse y
      open_source := C.inclusion_openEmbedding.isOpen_range
      open_target := isOpen_univ
      contMDiffOn_toFun := C.inverse_smooth
      contMDiffOn_invFun := C.inclusion_smooth.contMDiffOn }
  exact ⟨d, hx, fun _ _ => rfl⟩

end PoincareConjecture
