import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Maps.Proper.Basic










set_option autoImplicit false

open Set

namespace Homeomorph





theorem exists_union_of_compact {X Y : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y] {s u : Set X} {t v : Set Y}
    (hs : IsCompact s) (hu : IsCompact u) (e : s ≃ₜ t) (f : u ≃ₜ v)
    (hoverlap : ∀ x : s, (x : X) ∈ u ↔ (e x : Y) ∈ v)
    (hagree : ∀ (x : X) (hxs : x ∈ s) (hxu : x ∈ u),
      (e ⟨x, hxs⟩ : Y) = (f ⟨x, hxu⟩ : Y)) :
    ∃ H : (s ∪ u : Set X) ≃ₜ (t ∪ v : Set Y),
      (∀ x : s, (H ⟨x, Or.inl x.property⟩ : Y) = e x) ∧
      (∀ x : u, (H ⟨x, Or.inr x.property⟩ : Y) = f x) := by
  classical
  let F : (s ∪ u : Set X) → (t ∪ v : Set Y) := fun x =>
    if hx : (x : X) ∈ s then ⟨e ⟨x, hx⟩, Or.inl (e ⟨x, hx⟩).property⟩
    else ⟨f ⟨x, x.property.resolve_left hx⟩,
      Or.inr (f ⟨x, x.property.resolve_left hx⟩).property⟩
  have hFs (x : s) : F ⟨x, Or.inl x.property⟩ =
      ⟨e x, Or.inl (e x).property⟩ := by
    simp only [F, dif_pos x.property]
  have hFu (x : u) : F ⟨x, Or.inr x.property⟩ =
      ⟨f x, Or.inr (f x).property⟩ := by
    by_cases hx : (x : X) ∈ s
    · apply Subtype.ext
      simpa only [F, dif_pos hx] using hagree x hx x.property
    · simp only [F, dif_neg hx]
  let S : Set (s ∪ u : Set X) := {x | (x : X) ∈ s}
  let U : Set (s ∪ u : Set X) := {x | (x : X) ∈ u}
  have hcS : ContinuousOn F S := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : S =>
        (⟨e ⟨x.val.val, x.property⟩, Or.inl (e ⟨x.val.val, x.property⟩).property⟩ :
          (t ∪ v : Set Y))) := by fun_prop
    convert hc using 1
    funext x
    exact hFs ⟨x.val.val, x.property⟩
  have hcU : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun x : U =>
        (⟨f ⟨x.val.val, x.property⟩, Or.inr (f ⟨x.val.val, x.property⟩).property⟩ :
          (t ∪ v : Set Y))) := by fun_prop
    convert hc using 1
    funext x
    exact hFu ⟨x.val.val, x.property⟩
  have hcover : S ∪ U = univ := by
    apply eq_univ_of_forall
    intro x
    exact x.property
  have hc : Continuous F := by
    have h := hcS.union_of_isClosed hcU
      (hs.isClosed.preimage continuous_subtype_val) (hu.isClosed.preimage continuous_subtype_val)
    rw [hcover] at h
    exact continuousOn_univ.mp h
  have hcross (x : s) (y : u) (hxy : (e x : Y) = f y) : (x : X) = y := by
    have hxu : (x : X) ∈ u := (hoverlap x).mpr (hxy.symm ▸ (f y).property)
    have heq : f ⟨x, hxu⟩ = f y := Subtype.ext ((hagree x x.property hxu).symm.trans hxy)
    exact congrArg Subtype.val (f.injective heq)
  have hinj : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    rcases x.property with hx | hx <;> rcases y.property with hy | hy
    · have heq := congrArg Subtype.val hxy
      rw [hFs ⟨x, hx⟩, hFs ⟨y, hy⟩] at heq
      exact congrArg (fun z : s => (z : X)) (e.injective (Subtype.ext heq))
    · have heq := congrArg Subtype.val hxy
      rw [hFs ⟨x, hx⟩, hFu ⟨y, hy⟩] at heq
      exact hcross ⟨x, hx⟩ ⟨y, hy⟩ heq
    · have heq := congrArg Subtype.val hxy
      rw [hFu ⟨x, hx⟩, hFs ⟨y, hy⟩] at heq
      exact (hcross ⟨y, hy⟩ ⟨x, hx⟩ heq.symm).symm
    · have heq := congrArg Subtype.val hxy
      rw [hFu ⟨x, hx⟩, hFu ⟨y, hy⟩] at heq
      exact congrArg (fun z : u => (z : X)) (f.injective (Subtype.ext heq))
  have hsurj : Function.Surjective F := by
    intro y
    rcases y.property with hy | hy
    · let x := e.symm ⟨y, hy⟩
      refine ⟨⟨x, Or.inl x.property⟩, ?_⟩
      rw [hFs]
      apply Subtype.ext
      exact congrArg (fun z : t => (z : Y)) (e.apply_symm_apply ⟨y, hy⟩)
    · let x := f.symm ⟨y, hy⟩
      refine ⟨⟨x, Or.inr x.property⟩, ?_⟩
      rw [hFu]
      apply Subtype.ext
      exact congrArg (fun z : v => (z : Y)) (f.apply_symm_apply ⟨y, hy⟩)
  let : CompactSpace (s ∪ u : Set X) := isCompact_iff_compactSpace.mp (hs.union hu)
  let H := hc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hinj, hsurj⟩)
  exact ⟨H, fun x => congrArg Subtype.val (hFs x), fun x => congrArg Subtype.val (hFu x)⟩

end Homeomorph
