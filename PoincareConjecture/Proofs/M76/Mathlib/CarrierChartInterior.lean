import Mathlib.Topology.Homeomorph.Lemmas











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]






theorem injOn_and_interior_image_of_carrier_neighborhood
    {s d a : Set X} {C : Set Y} (e : d ≃ₜ C) (f : X → Y)
    (he : ∀ x : d, (e x : Y) = f x) (hds : d ⊆ s) (had : a ⊆ d)
    {p : X} (hp : p ∈ d)
    (hint : (e ⟨p, hp⟩ : Y) ∈ interior C)
    (ha : (Subtype.val ⁻¹' a : Set s) ∈ 𝓝 (⟨p, hds hp⟩ : s)) :
    InjOn f a ∧ f p ∈ interior (f '' a) := by
  let j : d → s := fun x => ⟨x, hds x.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hjp : Tendsto j (𝓝 (⟨p, hp⟩ : d)) (𝓝 (⟨p, hds hp⟩ : s)) :=
    hj.continuousAt
  have hna : (Subtype.val ⁻¹' a : Set d) ∈ 𝓝 (⟨p, hp⟩ : d) :=
    hjp.eventually ha
  have hmap : map (fun x : d => (e x : Y)) (𝓝 (⟨p, hp⟩ : d)) =
      𝓝 (e ⟨p, hp⟩ : Y) := by
    change map (Subtype.val ∘ e) (𝓝 (⟨p, hp⟩ : d)) = _
    rw [← map_map, e.map_nhds_eq, map_nhds_subtype_val,
      nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hint)]
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    have hxy' : e ⟨x, had hx⟩ = e ⟨y, had hy⟩ := by
      apply Subtype.ext
      simpa only [he] using hxy
    exact congrArg Subtype.val (e.injective hxy')
  · have him : f '' a ∈ map (fun x : d => (e x : Y)) (𝓝 (⟨p, hp⟩ : d)) := by
      change {x : d | (e x : Y) ∈ f '' a} ∈ 𝓝 (⟨p, hp⟩ : d)
      exact mem_of_superset hna (fun x hx => ⟨x, hx, (he x).symm⟩)
    rw [hmap, he] at him
    exact mem_interior_iff_mem_nhds.mpr him

end Homeomorph
