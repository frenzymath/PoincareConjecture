import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalIntervalBundle

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem prismFiberInterpolation_midpoint {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B) (x : B) :
    prismFiberInterpolation H x fiberMidHeight = prismFiberMidpoint H x := by
  unfold prismFiberInterpolation prismFiberPoint prismFiberMidpoint
  apply congrArg H
  apply Subtype.ext
  change ((H.symm x : E × ℝ).1,
    (1-(1/2 : ℝ))*(H.symm x : E × ℝ).2+(1/2 : ℝ)*(1-(H.symm x : E × ℝ).2)) =
      ((H.symm x : E × ℝ).1,(1/2 : ℝ))
  apply Prod.ext
  · rfl
  · ring

theorem interval_bundle_zero_section_value
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (m : C((⋃ i, B i), (⋃ i, B i)))
    (hm : ∀ i (x : B i), (m ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : E) =
      prismFiberMidpoint (H i) x)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i))) (hτ : Function.Involutive τ)
    (W : TwistedInvolutionInterval.Model τ hτ ≃ₜ (⋃ i, B i : Set E))
    (hW : ∀ z, W (TwistedInvolutionInterval.projection τ hτ z) = prismEndpointFiberMap H L z)
    (p : (⋃ i, prismEnds (H i) : Set E)) :
    W (TwistedInvolutionInterval.projection τ hτ (p,fiberMidHeight)) = m (prismEndpointInclusion H p) := by
  rw [hW]
  obtain ⟨i,⟨⟨a,b⟩,hp⟩⟩ := mem_iUnion.mp p.property
  have hp' : p = prismEndpointLift H i a b := Subtype.ext hp.symm
  rw [hp']
  apply Subtype.ext
  exact (hL i (prismEndMap (H i) a b) fiberMidHeight).trans
    ((congrArg Subtype.val (prismFiberInterpolation_midpoint (H i) (prismEndMap (H i) a b))).trans
      (hm i (prismEndMap (H i) a b)).symm)

theorem interval_bundle_zero_section_image
    {E ι : Type*} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀ i, (A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃ i, B i) × I, (⋃ i, B i)))
    (hL : ∀ i (x : B i) (t : I), (L (⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) x t)
    (m : C((⋃ i, B i), (⋃ i, B i)))
    (hm : ∀ i (x : B i), (m ⟨x,mem_iUnion.mpr ⟨i,x.property⟩⟩ : E) =
      prismFiberMidpoint (H i) x)
    (τ : (⋃ i, prismEnds (H i)) ≃ₜ (⋃ i, prismEnds (H i))) (hτ : Function.Involutive τ)
    (W : TwistedInvolutionInterval.Model τ hτ ≃ₜ (⋃ i, B i : Set E))
    (hW : ∀ z, W (TwistedInvolutionInterval.projection τ hτ z) = prismEndpointFiberMap H L z) :
    W '' TwistedInvolutionInterval.zeroSection τ hτ = range m := by
  apply Subset.antisymm
  · rintro x ⟨z,⟨⟨p,t⟩,ht,rfl⟩,rfl⟩
    have ht' : t = fiberMidHeight := ht
    rw [ht',interval_bundle_zero_section_value H L hL m hm τ hτ W hW]
    exact mem_range_self _
  · rintro x ⟨y,rfl⟩
    obtain ⟨p,hp⟩ := exists_endpoint_with_same_midpoint H m hm y
    exact ⟨TwistedInvolutionInterval.projection τ hτ (p,fiberMidHeight),
      ⟨(p,fiberMidHeight),rfl,rfl⟩,
      (interval_bundle_zero_section_value H L hL m hm τ hτ W hW p).trans hp⟩

end PoincareConjecture.M76.PrismBelt
