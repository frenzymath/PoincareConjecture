import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Source.StripComplement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.EndpointOrder
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Strips.RimEnds



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_unoriented_spanning_strip_complement
    {S T : Set P2}
    (hS : IsFinitePLBallPair P2 S (frontier S))
    (hT : IsFinitePLBallPair P2 T (frontier T)) (hST : S ⊆ interior T)
    (c : P2 → P2) (hc : FinitePiecewiseAffineOn c source) (hci : InjOn c source)
    (hin : MapsTo c source (T \ interior S))
    (hproper : ∀ p ∈ source, c p ∈ frontier T ∪ frontier S ↔ p.1 = 0 ∨ p.1 = 1)
    (houter : (c '' arm 0 ∩ frontier T).Nonempty)
    (hinner : (c '' arm 0 ∩ frontier S).Nonempty) :
    ∃ E : Set P2, IsFinitePLBallPair P2 E (frontier E) ∧
      E ∪ c '' source = T \ interior S ∧
      E ∩ (c '' source) = c '' (arm (-1) ∪ arm 1) ∧
      E ⊆ T \ interior S ∧
      frontier E = (E ∩ (frontier T ∪ frontier S)) ∪ c '' (arm (-1) ∪ arm 1) := by
  have hdis : Disjoint (frontier T) (frontier S) :=
    disjoint_left.mpr (fun x hxT hxS => hxT.2 (hST (hS.1 hxS)))
  rcases spanning_center_endpoint_order c hdis hproper houter hinner with horder | horder
  · obtain ⟨h0,h1⟩ := proper_strip_separate_rims hc.continuousOn isClosed_frontier
      isClosed_frontier hdis hproper horder.1 horder.2
    exact exists_spanning_strip_complement hS hT hST c hc hci hin h0 h1
  · let c' := c ∘ spanningSourceReverse
    have hc' : FinitePiecewiseAffineOn c' source :=
      hc.comp spanningSourceReverse_finitePL spanningSourceReverse_mapsTo
    have hi' : InjOn c' source := by
      intro x hx y hy hxy
      exact spanningSourceReverse_involutive.injective
        (hci (spanningSourceReverse_mapsTo hx) (spanningSourceReverse_mapsTo hy) hxy)
    have hp' : ∀ p ∈ source, c' p ∈ frontier T ∪ frontier S ↔ p.1 = 0 ∨ p.1 = 1 := by
      intro p hp
      change c (spanningSourceReverse p) ∈ frontier T ∪ frontier S ↔ _
      rw [hproper _ (spanningSourceReverse_mapsTo hp),spanningSourceReverse_apply]
      dsimp only
      constructor <;> rintro (h|h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    have hzero : c' (0,0) ∈ frontier T := by
      simpa only [c',Function.comp_apply,spanningSourceReverse_apply,sub_zero] using horder.2
    have hone : c' (1,0) ∈ frontier S := by
      simpa only [c',Function.comp_apply,spanningSourceReverse_apply,sub_self] using horder.1
    obtain ⟨h0,h1⟩ := proper_strip_separate_rims hc'.continuousOn isClosed_frontier
      isClosed_frontier hdis hp' hzero hone
    have hsource : c' '' source = c '' source := by
      rw [show c' = c ∘ spanningSourceReverse from rfl,image_comp,spanningSourceReverse_image]
    have harms : c' '' (arm (-1) ∪ arm 1) = c '' (arm (-1) ∪ arm 1) := by
      rw [show c' = c ∘ spanningSourceReverse from rfl,image_comp,image_union,
        spanningSourceReverse_arm_image,spanningSourceReverse_arm_image]
    simpa only [hsource,harms] using exists_spanning_strip_complement hS hT hST c' hc' hi'
      (hin.comp spanningSourceReverse_mapsTo) h0 h1

end PoincareConjecture.M76.Dehn.Annuli
