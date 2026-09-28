import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Tubes.WholeTraces

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_original_interval_strip_of_translated
    {X : Type*} {S C : Set P2} {U : Set X} {f g : P2 → X}
    (a : P2 ≃ᴬ[ℝ] P2) (d : P2 → P2)
    (hd : FinitePiecewiseAffineOn d source)
    (hdi : IsEmbedding (fun p : source => d p))
    (hmap : MapsTo d source (a '' S))
    (hkeep : ∀ x ∈ S, f (a x) = g x)
    (hpre : (a '' S) ∩ f ⁻¹' U = d '' source)
    (hcenter : d '' arm 0 = a '' C) :
    ∃ c : P2 → P2, FinitePiecewiseAffineOn c source ∧
      IsEmbedding (fun p : source => c p) ∧ MapsTo c source S ∧
      (∀ p, a (c p) = d p) ∧
      (∀ p ∈ source, g (c p) = f (d p)) ∧
      S ∩ g ⁻¹' U = c '' source ∧ c '' arm 0 = C := by
  let c := a.symm ∘ d
  have hval (p : P2) : a (c p) = d p := a.apply_symm_apply _
  have hmapC : MapsTo c source S := by
    intro p hp
    obtain ⟨x,hx,heq⟩ := hmap hp
    have hc : c p = x := by
      change a.symm (d p) = x
      rw [←heq,a.symm_apply_apply]
    exact hc.symm ▸ hx
  have heq (p : P2) (hp : p ∈ source) : g (c p) = f (d p) := by
    rw [←hkeep (c p) (hmapC hp),hval]
  refine ⟨c,hd.postcomp a.symm.toContinuousAffineMap,
    a.symm.toHomeomorph.isEmbedding.comp hdi,hmapC,hval,heq,?_,?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hx,hxU⟩
      have hax : a x ∈ (a '' S) ∩ f ⁻¹' U :=
        ⟨⟨x,hx,rfl⟩,show f (a x) ∈ U from (hkeep x hx).symm ▸ hxU⟩
      obtain ⟨p,hp,hpx⟩ := hpre.subset hax
      exact ⟨p,hp,a.injective ((hval p).trans hpx)⟩
    · rintro x ⟨p,hp,rfl⟩
      have hdU := (hpre.symm.subset ⟨p,hp,rfl⟩).2
      exact ⟨hmapC hp,show g (c p) ∈ U from (heq p hp).symm ▸ hdU⟩
  · apply a.injective.image_injective
    rw [image_image]
    change (a ∘ c) '' arm 0 = a '' C
    have ha : a ∘ c = d := funext hval
    rw [ha,hcenter]

end PoincareConjecture.M76.Dehn.Annuli
