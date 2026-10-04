import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Actual connected components under an ambient motion

Restricting the ambient homeomorphism constructs the correspondence of
component classes and of their actual carriers. The carrier maps have the
literal ambient point values, so marks can be transported through them.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76

variable {X : Type*} [TopologicalSpace X]

/-- The ambient inverse motion induces a homeomorphism on the spaces of
actual connected components, with its value on every represented class. -/
theorem exists_components_homeomorph_image_symm (F : X ≃ₜ X) (P : Set X) :
    ∃ H : ConnectedComponents P ≃ₜ ConnectedComponents (F.symm '' P : Set X),
      ∀ x : P, H (ConnectedComponents.mk x) =
        ConnectedComponents.mk (⟨F.symm x, mem_image_of_mem F.symm x.property⟩ :
          (F.symm '' P : Set X)) := by
  let e := F.symm.image P
  refine ⟨{
    toFun := e.continuous.connectedComponentsMap
    invFun := e.symm.continuous.connectedComponentsMap
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := e.continuous.connectedComponentsMap_continuous
    continuous_invFun := e.symm.continuous.connectedComponentsMap_continuous }, ?_⟩
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp only [Continuous.connectedComponentsMap_mk, e.symm_apply_apply]
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simp only [Continuous.connectedComponentsMap_mk, e.apply_symm_apply]
  · intro x
    rfl

/-- The moved component is exactly the ambient image of the old one. -/
theorem image_symm_connectedComponentIn (F : X ≃ₜ X) {P : Set X}
    {x : X} (hx : x ∈ P) :
    F.symm '' connectedComponentIn P x =
      connectedComponentIn (F.symm '' P) (F.symm x) :=
  F.symm.image_connectedComponentIn hx

/-- The restriction to the actual component has the prescribed point values. -/
theorem exists_component_homeomorph_image_symm (F : X ≃ₜ X) {P : Set X}
    {x : X} (hx : x ∈ P) :
    ∃ H : connectedComponentIn P x ≃ₜ
        connectedComponentIn (F.symm '' P) (F.symm x),
      ∀ y, (H y : X) = F.symm y := by
  exact ⟨(F.symm.image (connectedComponentIn P x)).trans
    (Homeomorph.setCongr (image_symm_connectedComponentIn F hx)), fun _ => rfl⟩

/-- A fixed model is homeomorphic to the actual moved component exactly when
it is homeomorphic to the corresponding old component. -/
theorem component_homeomorph_image_symm_iff (F : X ≃ₜ X) {P : Set X}
    {x : X} (hx : x ∈ P) (M : Type*) [TopologicalSpace M] :
    Nonempty (connectedComponentIn (F.symm '' P) (F.symm x) ≃ₜ M) ↔
      Nonempty (connectedComponentIn P x ≃ₜ M) := by
  obtain ⟨H, _⟩ := exists_component_homeomorph_image_symm F hx
  exact ⟨fun ⟨e⟩ => ⟨H.trans e⟩, fun ⟨e⟩ => ⟨H.symm.trans e⟩⟩

end PoincareMT.M76
