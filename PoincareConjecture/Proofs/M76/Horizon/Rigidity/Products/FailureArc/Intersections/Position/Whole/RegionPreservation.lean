import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusSides

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem proper_map_preserved_of_fixed_frontier_and_anchor
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {Source rim : Set E} {R : Set X} {f : E → X}
    (hf : ContinuousOn f Source) (hmap : MapsTo f Source R)
    (hproper : ∀ x ∈ Source, f x ∈ frontier R ↔ x ∈ rim)
    (hconnected : IsPreconnected (Source \ rim))
    (F : X ≃ₜ X) (hfrontier : EqOn F id (frontier R))
    {a : E} (ha : a ∈ Source \ rim) (hanchor : F (f a) = f a) :
    MapsTo (F ∘ f) Source R ∧
      (∀ x ∈ Source, (F ∘ f) x ∈ frontier R ↔ x ∈ rim) ∧
      EqOn (F ∘ f) f (Source ∩ rim) ∧
      MapsTo (F ∘ f) (Source \ rim) (interior R) := by
  have hfront (x : X) : F x ∈ frontier R ↔ x ∈ frontier R := by
    constructor
    · intro hx
      have heq : F x = x := F.injective (hfrontier hx)
      exact heq ▸ hx
    · intro hx
      simpa only [hfrontier hx, id_eq] using hx
  have hdisjoint : Disjoint ((F ∘ f) '' (Source \ rim)) (frontier R) := by
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    exact hx.2 ((hproper x hx.1).mp ((hfront (f x)).mp hy))
  have hinside : (F ∘ f) '' (Source \ rim) ⊆ interior R := by
    apply (hconnected.image (F ∘ f)
      (F.continuous.comp_continuousOn (hf.mono sdiff_subset))).subset_interior_of_avoids_frontier
      hdisjoint
    refine ⟨f a, ⟨a, ha, hanchor⟩, ?_⟩
    by_contra hn
    exact ha.2 ((hproper a ha.1).mp ⟨subset_closure (hmap ha.1), hn⟩)
  refine ⟨?_, fun x hx => (hfront (f x)).trans (hproper x hx), ?_, ?_⟩
  · intro x hx
    by_cases hxr : x ∈ rim
    · change F (f x) ∈ R
      rw [hfrontier ((hproper x hx).mpr hxr)]
      exact hmap hx
    · exact interior_subset (hinside (mem_image_of_mem (F ∘ f) ⟨hx, hxr⟩))
  · intro x hx
    exact hfrontier ((hproper x hx.1).mpr hx.2)
  · exact fun _ hx => hinside (mem_image_of_mem (F ∘ f) hx)

end PoincareConjecture.M76
