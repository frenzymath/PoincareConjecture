import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.RawPair
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.Decomposition

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

theorem opposite_source_of_equal_value
    {E X : Type*} {f : E → X} {S T : Set E}
    (hfiS : InjOn f S) (hfiT : InjOn f T)
    {x y : E} (hx : x ∈ S ∪ T) (hy : y ∈ S ∪ T)
    (hne : x ≠ y) (hxy : f x = f y) :
    (x ∈ S ∧ y ∈ T) ∨ (x ∈ T ∧ y ∈ S) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (hne (hfiS hx hy hxy)).elim
  · exact Or.inl ⟨hx,hy⟩
  · exact Or.inr ⟨hx,hy⟩
  · exact (hne (hfiT hx hy hxy)).elim

theorem disjoint_source_pair_unique
    {E X : Type*} {f : E → X} {S T : Set E}
    (hdis : Disjoint S T) (hfiS : InjOn f S) (hfiT : InjOn f T)
    {x y z : E} (hx : x ∈ S ∪ T) (hy : y ∈ S ∪ T) (hz : z ∈ S ∪ T)
    (hxy : x ≠ y) (hxz : x ≠ z) (hfxy : f x = f y) (hfxz : f x = f z) : y = z := by
  rcases opposite_source_of_equal_value hfiS hfiT hx hy hxy hfxy with h | h <;>
    rcases opposite_source_of_equal_value hfiS hfiT hx hz hxz hfxz with k | k
  · exact hfiT h.2 k.2 (hfxy.symm.trans hfxz)
  · exact (disjoint_left.mp hdis h.1 k.1).elim
  · exact (disjoint_left.mp hdis k.1 h.1).elim
  · exact hfiS h.2 k.2 (hfxy.symm.trans hfxz)

theorem double_locus_disjoint_source_pair
    {E X : Type*} {f : E → X} {S T : Set E}
    (hdis : Disjoint S T) (hfiS : InjOn f S) (hfiT : InjOn f T) :
    doubleLocusOn f (S ∪ T) =
      {x | x ∈ S ∧ f x ∈ f '' T} ∪ {y | y ∈ T ∧ f y ∈ f '' S} := by
  ext x
  constructor
  · rintro ⟨hx,y,hy,hxy,hne⟩
    rcases opposite_source_of_equal_value hfiS hfiT hx hy hne hxy with h | h
    · exact Or.inl ⟨h.1,⟨y,h.2,hxy.symm⟩⟩
    · exact Or.inr ⟨h.1,⟨y,h.2,hxy.symm⟩⟩
  · rintro (⟨hx,y,hy,hyx⟩ | ⟨hx,y,hy,hyx⟩)
    · exact ⟨Or.inl hx,y,Or.inr hy,hyx.symm,
        fun h => disjoint_left.mp hdis hx (h.symm ▸ hy)⟩
    · exact ⟨Or.inr hx,y,Or.inl hy,hyx.symm,
        fun h => disjoint_left.mp hdis (h.symm ▸ hy) hx⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
