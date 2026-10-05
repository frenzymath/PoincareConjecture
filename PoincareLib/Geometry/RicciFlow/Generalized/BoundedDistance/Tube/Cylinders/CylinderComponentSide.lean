import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Cylinders.CylinderSphereSides

/-!
# Identify an actual full component with a cylinder half

An actual connected component of a sphere complement occupies exactly
one signed-height half. The component equality is used in the ambient
manifold, so no change of source carrier or component convention occurs.
Source: Morgan--Tian Claim 10.8, p. 254; M28 derivation 124.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT.M28

variable {M : Type*} [TopologicalSpace M] {U : TopologicalSpace.Opens M}

/-- The two possible signs of a genuine full component are exhaustive.
Both directions of membership are proved using its connectedness and
the maximality of its actual ambient component. Source: Claim 10.8,
p. 254; M28 derivation 124. -/
theorem cylinderSignedHeight_component_half
    (phi : U ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1)) {S F : Set M}
    (hzero : ∀ x : U, cylinderSignedHeight phi x = 0 ↔ (x : M) ∈ S)
    (hF : IsConnected F) (hFU : F ⊆ (U : Set M) \ S)
    (hcomponent : ∀ x ∈ F, connectedComponentIn ((U : Set M) \ S) x = F) :
    (∀ x : U, cylinderSignedHeight phi x < 0 ↔ (x : M) ∈ F) ∨
      (∀ x : U, 0 < cylinderSignedHeight phi x ↔ (x : M) ∈ F) := by
  obtain ⟨w, hw⟩ := hF.nonempty
  let wU : U := ⟨w, (hFU hw).1⟩
  have hFrange : F ⊆ range (Subtype.val : U → M) := by
    intro x hx
    exact ⟨⟨x, (hFU hx).1⟩, rfl⟩
  have hpre : IsPreconnected {x : U | (x : M) ∈ F} :=
    hF.isPreconnected.preimage_of_isOpenMap Subtype.val_injective
      U.isOpen.isOpenMap_subtype_val hFrange
  have havoid : ∀ x ∈ {x : U | (x : M) ∈ F}, cylinderSignedHeight phi x ≠ 0 := by
    intro x hx hh
    exact (hFU hx).2 ((hzero x).mp hh)
  have hwne : cylinderSignedHeight phi wU ≠ 0 := havoid wU hw
  rcases lt_or_gt_of_ne hwne with hwneg | hwpos
  · left
    have hhalf : IsPreconnected
        ((Subtype.val : U → M) '' {x : U | cylinderSignedHeight phi x < 0}) :=
      (isPreconnected_cylinderSignedHeight_negative phi).image _
        continuous_subtype_val.continuousOn
    have hhalfsub : (Subtype.val : U → M) '' {x : U | cylinderSignedHeight phi x < 0} ⊆
        (U : Set M) \ S := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.property, fun hxS => (ne_of_lt hx) ((hzero x).mpr hxS)⟩
    have hhalfF : (Subtype.val : U → M) '' {x : U | cylinderSignedHeight phi x < 0} ⊆
        F := by
      rw [← hcomponent w hw]
      exact hhalf.subset_connectedComponentIn ⟨wU, hwneg, rfl⟩ hhalfsub
    intro x
    exact ⟨fun hx => hhalfF ⟨x, hx, rfl⟩,
      fun hx => hpre.gt_of_ne (continuous_cylinderSignedHeight phi).continuousOn
        havoid ⟨wU, hw, hwneg⟩ hx⟩
  · right
    have hhalf : IsPreconnected
        ((Subtype.val : U → M) '' {x : U | 0 < cylinderSignedHeight phi x}) :=
      (isPreconnected_cylinderSignedHeight_positive phi).image _
        continuous_subtype_val.continuousOn
    have hhalfsub : (Subtype.val : U → M) '' {x : U | 0 < cylinderSignedHeight phi x} ⊆
        (U : Set M) \ S := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.property, fun hxS => (ne_of_gt hx) ((hzero x).mpr hxS)⟩
    have hhalfF : (Subtype.val : U → M) '' {x : U | 0 < cylinderSignedHeight phi x} ⊆
        F := by
      rw [← hcomponent w hw]
      exact hhalf.subset_connectedComponentIn ⟨wU, hwpos, rfl⟩ hhalfsub
    intro x
    exact ⟨fun hx => hhalfF ⟨x, hx, rfl⟩,
      fun hx => hpre.lt_of_ne (continuous_cylinderSignedHeight phi).continuousOn
        havoid ⟨wU, hw, hwpos⟩ hx⟩

end PoincareMT.M28
