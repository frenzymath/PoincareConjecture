import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousOn



set_option autoImplicit false
open Set

namespace ContinuousMap

theorem exists_product_union_of_isClosed
    {T X Y : Type*} [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    {S U : Set X} (hS : IsClosed S) (hU : IsClosed U)
    (G : C(T × S, Y)) (H : C(T × U, Y))
    (hagree : ∀ (t : T) (x : X) (hxS : x ∈ S) (hxU : x ∈ U),
      G (t, ⟨x, hxS⟩) = H (t, ⟨x, hxU⟩)) :
    ∃ F : C(T × ↥(S ∪ U), Y),
      (∀ (t : T) (x : S), F (t, ⟨x, Or.inl x.property⟩) = G (t, x)) ∧
      (∀ (t : T) (x : U), F (t, ⟨x, Or.inr x.property⟩) = H (t, x)) := by
  classical
  let f : T × ↥(S ∪ U) → Y := fun z =>
    if hx : (z.2 : X) ∈ S then G (z.1, ⟨z.2, hx⟩)
    else H (z.1, ⟨z.2, z.2.property.resolve_left hx⟩)
  have hfs (t : T) (x : S) : f (t, ⟨x, Or.inl x.property⟩) = G (t, x) := dif_pos x.property
  have hfu (t : T) (x : U) : f (t, ⟨x, Or.inr x.property⟩) = H (t, x) := by
    by_cases hx : (x : X) ∈ S
    · exact (dif_pos hx).trans (hagree t x hx x.property)
    · exact dif_neg hx
  let V : Set (T × ↥(S ∪ U)) := {z | (z.2 : X) ∈ S}
  let W : Set (T × ↥(S ∪ U)) := {z | (z.2 : X) ∈ U}
  have hfV : ContinuousOn f V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let k : V → T × S := fun z => (z.1.1, ⟨z.1.2, z.property⟩)
    have hk : Continuous k := by fun_prop
    convert G.continuous.comp hk using 1
    funext z
    exact hfs z.val.1 ⟨z.val.2, z.property⟩
  have hfW : ContinuousOn f W := by
    rw [continuousOn_iff_continuous_domRestrict]
    let k : W → T × U := fun z => (z.1.1, ⟨z.1.2, z.property⟩)
    have hk : Continuous k := by fun_prop
    convert H.continuous.comp hk using 1
    funext z
    exact hfu z.val.1 ⟨z.val.2, z.property⟩
  have hcover : V ∪ W = univ := eq_univ_of_forall fun z => z.2.property
  have hc : Continuous f := by
    have hh := hfV.union_of_isClosed hfW
      (hS.preimage (continuous_subtype_val.comp continuous_snd))
      (hU.preimage (continuous_subtype_val.comp continuous_snd))
    rw [hcover] at hh
    exact continuousOn_univ.mp hh
  exact ⟨⟨f, hc⟩, hfs, hfu⟩

end ContinuousMap
