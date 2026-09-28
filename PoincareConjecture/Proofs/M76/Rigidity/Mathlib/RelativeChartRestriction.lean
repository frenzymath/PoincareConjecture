import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set

namespace OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem IsImage.exists_subtype_chart
    {e : OpenPartialHomeomorph X Y} {A : Set X} {B : Set Y}
    (h : e.IsImage A B) (x : A) (hx : (x : X) ∈ e.source) :
    ∃ r : OpenPartialHomeomorph A B,
      r.source = (Subtype.val : A → X) ⁻¹' e.source ∧
      r.target = (Subtype.val : B → Y) ⁻¹' e.target ∧
      (∀ a ∈ r.source, (r a : Y) = e a) ∧
      ∀ b ∈ r.target, (r.symm b : X) = e.symm b := by
  let U : TopologicalSpace.Opens A :=
    ⟨(Subtype.val : A → X) ⁻¹' e.source,
      e.open_source.preimage continuous_subtype_val⟩
  let V : TopologicalSpace.Opens B :=
    ⟨(Subtype.val : B → Y) ⁻¹' e.target,
      e.open_target.preimage continuous_subtype_val⟩
  let f : U ≃ₜ V :=
    { toFun := fun a =>
        ⟨⟨e (a.val : X), (h.apply_mem_iff a.property).mpr a.val.property⟩,
          e.map_source a.property⟩
      invFun := fun b =>
        ⟨⟨e.symm (b.val : Y), (h.symm_apply_mem_iff b.property).mpr b.val.property⟩,
          e.map_target b.property⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        exact e.left_inv a.property
      right_inv := by
        intro b
        apply Subtype.ext
        apply Subtype.ext
        exact e.right_inv b.property
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact e.continuousOn.comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val) (fun a => a.property)
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact e.symm.continuousOn.comp_continuous
          (continuous_subtype_val.comp continuous_subtype_val) (fun b => b.property) }
  let u0 : U := ⟨x, hx⟩
  let iu := U.openPartialHomeomorphSubtypeCoe ⟨u0⟩
  let iv := V.openPartialHomeomorphSubtypeCoe ⟨f u0⟩
  have hiuS : iu.source = univ := rfl
  have hiuT : iu.target = (U : Set A) := U.openPartialHomeomorphSubtypeCoe_target ⟨u0⟩
  have hivS : iv.source = univ := rfl
  have hivT : iv.target = (V : Set B) := V.openPartialHomeomorphSubtypeCoe_target ⟨f u0⟩
  let r := iu.symm.trans (f.toOpenPartialHomeomorph.trans iv)
  have hrS : r.source = (Subtype.val : A → X) ⁻¹' e.source := by
    dsimp only [r]
    simp only [trans_source, symm_source, Homeomorph.toOpenPartialHomeomorph_source,
      hivS, preimage_univ, inter_univ, hiuT]
    rfl
  have hrT : r.target = (Subtype.val : B → Y) ⁻¹' e.target := by
    dsimp only [r]
    simp only [trans_target, symm_target, Homeomorph.toOpenPartialHomeomorph_target,
      hiuS, preimage_univ, inter_univ, hivT]
    rfl
  refine ⟨r, hrS, hrT, ?_, ?_⟩
  · intro a ha
    let u : U := ⟨a, by rwa [hrS] at ha⟩
    have hiu : iu.symm a = u := iu.left_inv (x := u) (mem_univ u)
    change (f (iu.symm a) : Y) = e a
    rw [hiu]
    rfl
  · intro b hb
    let v : V := ⟨b, by rwa [hrT] at hb⟩
    have hiv : iv.symm b = v := iv.left_inv (x := v) (mem_univ v)
    change (f.symm (iv.symm b) : X) = e.symm b
    rw [hiv]
    rfl

end OpenPartialHomeomorph
