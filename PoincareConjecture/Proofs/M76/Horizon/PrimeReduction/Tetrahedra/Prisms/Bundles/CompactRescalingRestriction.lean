import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem exists_compact_rescaling_restriction
    {E : Type*} [TopologicalSpace E] [T2Space E]
    (A B S : Set E) (hA : IsCompact A) (r : E → E)
    (hr : ContinuousOn r A) (himage : r '' A = B)
    (hinj : InjOn r (A \ r ⁻¹' S)) :
    ∃ T : (A \ r ⁻¹' S : Set E) ≃ₜ (B \ S : Set E), ∀x, (T x : E) = r x := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let f : A → B := fun x => ⟨r x, himage ▸ mem_image_of_mem r x.property⟩
  have hf : Continuous f := hr.domRestrict.codRestrict _
  let V : Set B := {y | (y : E) ∉ S}
  have hbij : Function.Bijective (V.restrictPreimage f) := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact hinj ⟨x.val.property,x.property⟩ ⟨y.val.property,y.property⟩
        (congrArg (fun z : V => (z.val : E)) h)
    · intro y
      obtain ⟨x,hx,hxy⟩ := show (y.val : E) ∈ r '' A by rw [himage]; exact y.val.property
      refine ⟨⟨⟨x,hx⟩,?_⟩,?_⟩
      · change r x ∉ S
        rw [hxy]
        exact y.property
      · apply Subtype.ext
        exact Subtype.ext hxy
  let e := (Equiv.ofBijective (V.restrictPreimage f) hbij).toHomeomorphOfContinuousClosed
    hf.restrictPreimage (hf.isClosedMap.restrictPreimage V)
  let a : (A \ r ⁻¹' S : Set E) ≃ₜ (f ⁻¹' V) :=
    { toFun := fun x => ⟨⟨x,x.property.1⟩,x.property.2⟩
      invFun := fun x => ⟨x.val, x.val.property,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  let b : V ≃ₜ (B \ S : Set E) :=
    { toFun := fun x => ⟨x.val,x.val.property,x.property⟩
      invFun := fun x => ⟨⟨x,x.property.1⟩,x.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact ⟨a.trans (e.trans b),fun _ => rfl⟩

end PoincareConjecture.M76.PrismBelt
