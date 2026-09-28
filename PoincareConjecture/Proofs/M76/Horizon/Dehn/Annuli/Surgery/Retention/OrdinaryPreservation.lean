import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.Compactness
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Components.LocalInjectivity

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem ordinary_crossings_preserved_by_retained_copy
    {E Y X ι : Type*} [TopologicalSpace E] [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {g : Y → X}
    {K S U : Set E} {T V : Set Y} {R : Set X}
    (hKS : K ⊆ S) (hK : IsClosed K) (hS : IsCompact S) (hT : IsCompact T)
    (hG : IsCompact (doubleLocusOn f S))
    (p : doubleLocusOn f S → doubleLocusOn f S) (hp : Continuous p)
    (hvalue : ∀ x, f (p x) = f x) (hfree : ∀ x, (p x : E) ≠ x)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E))
    (hinterior : MapsTo f (doubleLocusOn f S) (interior R))
    (hcross : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f S R x y))
    (j : K → Y) (hji : Function.Injective j) (hjc : Continuous j)
    (hjkeep : ∀ x, g (j x) = f x)
    (hrel : {v : Y × Y | v.1 ∈ T ∧ v.2 ∈ T ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : K × K ↦ (j v.1, j v.2)) ''
        {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2})
    (hnew : doubleLocusOn g T =
      j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y})
    (hUS : U ⊆ S) (hVT : V ⊆ T)
    (hU : IsOpen ((Subtype.val : S → E) ⁻¹' U))
    (hV : IsOpen ((Subtype.val : T → Y) ⁻¹' V))
    (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (H : U ≃ₜ V) (hHkeep : ∀ x : U, g (H x) = f x)
    (hcontains : doubleLocusOn g T ⊆ V) :
    IsCompact (doubleLocusOn g T) ∧ IsClosed (doubleLocusOn g T) ∧
      MapsTo g (doubleLocusOn g T) (interior R) ∧
      (∀ x ∈ T, ∀ y ∈ T, ∀ z ∈ T,
        x ≠ y → x ≠ z → g x = g y → g x = g z → y = z) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → g x = g y →
        Nonempty (RawSourceCrossing e g T R x y)) ∧
      IsLocallyInjective (fun x : T ↦ g x) := by
  have hc := isCompact_new_double_locus_of_retained hKS hK hG p hp hvalue hfree
    hunique j hjc hnew
  have hraw : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → g x = g y →
      Nonempty (RawSourceCrossing e g T R x y) := by
    intro x hx y hy hne hxy
    exact raw_source_crossings_of_retained_open_copy hS hT hUS hVT hU hV hf hg H
      hHkeep p hunique hcontains (fun a ha b hb hab hne ↦ hcross a ha b hb hne hab)
      x hx y hy hxy hne
  refine ⟨hc, hc.isClosed, ?_, ?_, hraw,
    isLocallyInjective_of_raw_source_crossings hc.isClosed hraw⟩
  · intro x hx
    obtain ⟨a, ⟨b, hab, hne⟩, rfl⟩ := hnew.subset hx
    rw [hjkeep]
    exact hinterior ⟨hKS a.property, b, hKS b.property, hab, hne⟩
  · intro x hx y hy z hz hxy hxz heq₁ heq₂
    apply retained_relation_unique_other_point hKS j hji hrel
      (fun a ha b hb c hc hab hac hnab hnac ↦ ?_) x y z hx hy hz heq₁ heq₂ hxy hxz
    let a' : doubleLocusOn f S := ⟨a, ha, b, hb, hab, hnab⟩
    exact (hunique a' b hb hab hnab).trans (hunique a' c hc hac hnac).symm

end PoincareConjecture.M76.Dehn.Annuli
