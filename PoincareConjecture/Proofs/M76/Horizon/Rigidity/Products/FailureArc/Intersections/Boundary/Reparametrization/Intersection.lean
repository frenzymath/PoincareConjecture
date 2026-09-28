import Mathlib.Topology.Homeomorph.Lemmas
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Arcs.Models

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem image_eq_of_source_homeomorph
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S : Set E} {T : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X}
    (hvalue : ∀ x : S, f x = g (H x)) : f '' S = g '' T := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, (hvalue ⟨x, hx⟩).symm⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨H.symm ⟨y, hy⟩, (H.symm ⟨y, hy⟩).property, ?_⟩
    simpa only [H.apply_symm_apply] using hvalue (H.symm ⟨y, hy⟩)

def intersectionSourceHomeomorph
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S : Set E} {T : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X} (A : Set X)
    (hvalue : ∀ x : S, f x = g (H x)) :
    (S ∩ f ⁻¹' A : Set E) ≃ₜ (T ∩ g ⁻¹' A : Set Y) where
  toFun x := ⟨H ⟨x, x.property.1⟩, (H ⟨x, x.property.1⟩).property,
    by change g (H ⟨x, x.property.1⟩) ∈ A; rw [← hvalue]; exact x.property.2⟩
  invFun y := ⟨H.symm ⟨y, y.property.1⟩, (H.symm ⟨y, y.property.1⟩).property,
    by change f (H.symm ⟨y, y.property.1⟩) ∈ A; rw [hvalue, H.apply_symm_apply]; exact y.property.2⟩
  left_inv x := Subtype.ext (congrArg (fun z : S ↦ (z : E))
    (H.symm_apply_apply ⟨x, x.property.1⟩))
  right_inv y := Subtype.ext (congrArg (fun z : T ↦ (z : Y))
    (H.apply_symm_apply ⟨y, y.property.1⟩))
  continuous_toFun := (continuous_subtype_val.comp
    (H.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp
    (H.symm.continuous.comp (continuous_subtype_val.subtype_mk _))).subtype_mk _

theorem intersection_component_count_source_homeomorph
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S : Set E} {T : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X} (A : Set X)
    (hvalue : ∀ x : S, f x = g (H x)) :
    Nat.card (ConnectedComponents (S ∩ f ⁻¹' A : Set E)) =
      Nat.card (ConnectedComponents (T ∩ g ⁻¹' A : Set Y)) := by
  let D := intersectionSourceHomeomorph H A hvalue
  let C := D.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y ↦ by
    have hfiber : D ⁻¹' {y} = {D.symm y} := by
      ext x
      exact D.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton
  exact Nat.card_congr C.toEquiv

theorem intersection_components_meet_set_source_homeomorph
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y]
    {S Q : Set E} {T P : Set Y} (H : S ≃ₜ T) {f : E → X} {g : Y → X} {A : Set X}
    (hvalue : ∀ x : S, f x = g (H x))
    (hmark : ∀ x : S, (H x : Y) ∈ P ↔ (x : E) ∈ Q)
    (hmeet : ∀ x : (T ∩ g ⁻¹' A : Set Y), ∃ y : (T ∩ g ⁻¹' A : Set Y),
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : Y) ∈ P) :
    ∀ x : (S ∩ f ⁻¹' A : Set E), ∃ y : (S ∩ f ⁻¹' A : Set E),
      ConnectedComponents.mk x = ConnectedComponents.mk y ∧ (y : E) ∈ Q := by
  let D := intersectionSourceHomeomorph H A hvalue
  let C := D.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y ↦ by
    have hfiber : D ⁻¹' {y} = {D.symm y} := by
      ext x
      exact D.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton
  have hC (x : (S ∩ f ⁻¹' A : Set E)) :
      C (ConnectedComponents.mk x) = ConnectedComponents.mk (D x) := rfl
  intro x
  obtain ⟨y, hxy, hyP⟩ := hmeet (D x)
  refine ⟨D.symm y, C.injective ?_, ?_⟩
  · rw [hC, hC, D.apply_symm_apply]
    exact hxy
  · apply (hmark ⟨D.symm y, (D.symm y).property.1⟩).mp
    change (D (D.symm y) : Y) ∈ P
    rwa [D.apply_symm_apply]

end PoincareConjecture.M76.Dehn.Annuli
