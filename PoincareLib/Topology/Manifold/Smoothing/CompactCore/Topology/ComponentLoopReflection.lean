import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Connected.Basic

/-!
# Loop homotopies remain in their actual whole component

The connected image of the homotopy square contains the original
basepoint, hence lies in its actual connected component. Restricting
the map reflects homotopy through the original component inclusion.
See Wall005, component scope, and Wall019, lines 133--143.
-/

set_option autoImplicit false

open Set

namespace Path.Homotopic

/-- Pull the actual mapped homotopy back through the retained homeomorphism. -/
theorem of_map_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) {a b : X} {p q : Path a b}
    (h : (p.map H.continuous).Homotopic (q.map H.continuous)) : p.Homotopic q := by
  obtain ⟨L⟩ := h
  refine ⟨{
    toFun := fun z => H.symm (L z)
    continuous_toFun := H.symm.continuous.comp L.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact (congrArg H.symm (L.map_zero_left t)).trans (H.symm_apply_apply _)
  · intro t
    exact (congrArg H.symm (L.map_one_left t)).trans (H.symm_apply_apply _)
  · intro t x hx
    exact (congrArg H.symm (L.prop t x hx)).trans (H.symm_apply_apply _)

/-- An endpoint cast retains an actual contraction. -/
theorem cast_refl {X : Type*} [TopologicalSpace X] {a b : X} {p : Path a a}
    (h : p.Homotopic (Path.refl a)) (hab : b = a) :
    (p.cast hab hab).Homotopic (Path.refl b) := by
  subst b
  exact h

/-- Reflect homotopy through inclusion of an actual whole component.
No retract, openness or new homotopy is assumed. -/
theorem of_map_whole_component
    {X : Type*} [TopologicalSpace X] {S F : Set X} (hSF : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    {a b : S} {p q : Path a b}
    (h : (p.map (continuous_inclusion hSF)).Homotopic
      (q.map (continuous_inclusion hSF))) : p.Homotopic q := by
  obtain ⟨H⟩ := h
  let f : unitInterval × unitInterval → X := fun z => (H z : X)
  have hf : Continuous f := continuous_subtype_val.comp H.continuous
  have ha : (a : X) ∈ range f := by
    refine ⟨(0, 0), ?_⟩
    exact congrArg Subtype.val ((H.map_zero_left 0).trans (p.map (continuous_inclusion hSF)).source)
  have hF : range f ⊆ F := by
    rintro _ ⟨z, rfl⟩
    exact (H z).property
  have hS : range f ⊆ S := by
    rw [← hcomponent a a.property]
    exact (isPreconnected_range hf).subset_connectedComponentIn ha hF
  refine ⟨{
    toFun := fun z => ⟨H z, hS (mem_range_self z)⟩
    continuous_toFun := hf.subtype_mk _
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact Subtype.ext (congrArg (fun y : F => (y : X)) (H.map_zero_left t))
  · intro t
    exact Subtype.ext (congrArg (fun y : F => (y : X)) (H.map_one_left t))
  · intro t x hx
    exact Subtype.ext (congrArg (fun y : F => (y : X)) (H.prop t x hx))

end Path.Homotopic
