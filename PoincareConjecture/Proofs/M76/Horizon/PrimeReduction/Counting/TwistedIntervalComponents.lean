import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.TwistedInvolutionInterval
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set CategoryTheory Limits
open scoped Topology
universe u
namespace PoincareConjecture.M76.TwistedInvolutionInterval

variable {S : Type u} [TopologicalSpace S] (τ : S ≃ₜ S)
  (hτ : Function.Involutive τ)

def componentImage (x : S) : Set (Model τ hτ) :=
  projection τ hτ '' (connectedComponent x ×ˢ (univ : Set unitInterval))

theorem componentImage_eq [LocallyConnectedSpace S] (x : S) :
    componentImage τ hτ x = connectedComponent (boundaryMap τ hτ x) := by
  have hpre : projection τ hτ ⁻¹' componentImage τ hτ x =
      (connectedComponent x ×ˢ (univ : Set unitInterval)) ∪
        (deck τ) ⁻¹' (connectedComponent x ×ˢ (univ : Set unitInterval)) := by
    ext z
    constructor
    · rintro ⟨w,hw,he⟩
      rcases (projection_eq τ hτ w z).mp he with rfl | he
      · exact Or.inl hw
      · exact Or.inr (by
          change deck τ z ∈ connectedComponent x ×ˢ (univ : Set unitInterval)
          rw [← he]
          exact hw)
    · rintro (hz | hz)
      · exact ⟨z,hz,rfl⟩
      · exact ⟨deck τ z,hz,projection_deck τ hτ z⟩
  have hopen : IsOpen (componentImage τ hτ x) := by
    apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
    change IsOpen (projection τ hτ ⁻¹' componentImage τ hτ x)
    rw [hpre]
    exact ((isOpen_connectedComponent : IsOpen (connectedComponent x)).prod isOpen_univ).union
      (((isOpen_connectedComponent : IsOpen (connectedComponent x)).prod isOpen_univ).preimage
        (deck τ).continuous)
  have hclosed : IsClosed (componentImage τ hτ x) :=
    FreeInvolutionQuotient.projection_isClosedMap _ _ _
      (isClosed_connectedComponent.prod isClosed_univ)
  have hconn : IsConnected (componentImage τ hτ x) :=
    (isConnected_connectedComponent.prod isConnected_univ).image _
      (continuous_projection τ hτ).continuousOn
  have hx : boundaryMap τ hτ x ∈ componentImage τ hτ x :=
    ⟨(x,0),⟨mem_connectedComponent,mem_univ _⟩,rfl⟩
  exact (hconn.subset_connectedComponent hx).antisymm
    (isPreconnected_connectedComponent.subset_isClopen ⟨hclosed,hopen⟩
      ⟨_,mem_connectedComponent,hx⟩)

include hτ in
theorem connectedComponent_invariant {x : S} (hx : τ x ∈ connectedComponent x) :
    ∀ y, y ∈ connectedComponent x ↔ τ y ∈ connectedComponent x := by
  have hmap : MapsTo τ (connectedComponent x) (connectedComponent x) := by
    intro y hy
    have h := τ.continuous.image_connectedComponent_subset x ⟨y,hy,rfl⟩
    rwa [← connectedComponent_eq hx] at h
  intro y
  exact ⟨fun hy => hmap hy,fun hy => hτ y ▸ hmap hy⟩

def componentInvolution {x : S} (hx : τ x ∈ connectedComponent x) :
    connectedComponent x ≃ₜ connectedComponent x :=
  τ.subtype (connectedComponent_invariant τ hτ hx)

theorem componentInvolution_involutive {x : S} (hx : τ x ∈ connectedComponent x) :
    Function.Involutive (componentInvolution τ hτ hx) := by
  intro y
  exact Subtype.ext (hτ y)

theorem exists_invariant_component_homeomorph [CompactSpace S] [T2Space S]
    [LocallyConnectedSpace S] (x : S) (hx : τ x ∈ connectedComponent x) :
    ∃ W : Model (componentInvolution τ hτ hx) (componentInvolution_involutive τ hτ hx) ≃ₜ
        connectedComponent (boundaryMap τ hτ x),
      ∀ z, (W (projection _ _ z) : Model τ hτ) = projection τ hτ (z.1.val,z.2) := by
  let C := connectedComponent x
  let : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let θ := componentInvolution τ hτ hx
  let hθ := componentInvolution_involutive τ hτ hx
  let f : C × unitInterval → connectedComponent (boundaryMap τ hτ x) := fun z =>
    ⟨projection τ hτ (z.1.val,z.2),(componentImage_eq τ hτ x).le
      ⟨(z.1.val,z.2),⟨z.1.property,mem_univ _⟩,rfl⟩⟩
  have hf : Continuous f := ((continuous_projection τ hτ).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _
  have hresp : ∀ a b, (FreeInvolutionQuotient.orbitSetoid (deck θ)
      (deck_involutive θ hθ)).r a b → f a = f b := by
    intro a b hab
    apply Subtype.ext
    apply (projection_eq τ hτ _ _).mpr
    rcases hab with rfl | hab
    · exact Or.inl rfl
    · exact Or.inr (congrArg (fun z : C × unitInterval => (z.1.val,z.2)) hab)
  let φ : Model θ hθ → connectedComponent (boundaryMap τ hτ x) := Quotient.lift f hresp
  have hc : Continuous φ := hf.quotient_lift hresp
  have hi : Function.Injective φ := by
    intro z w
    induction z using Quotient.inductionOn with | _ a =>
      induction w using Quotient.inductionOn with | _ b =>
        intro hab
        apply (projection_eq θ hθ a b).mpr
        have he := (projection_eq τ hτ _ _).mp (congrArg Subtype.val hab)
        rcases he with he | he
        · apply Or.inl
          apply Prod.ext
          · exact Subtype.ext (congrArg Prod.fst he)
          · exact congrArg (fun z : S × unitInterval => z.2) he
        · apply Or.inr
          apply Prod.ext
          · exact Subtype.ext (congrArg Prod.fst he)
          · exact congrArg (fun z : S × unitInterval => z.2) he
  have hs : Function.Surjective φ := by
    rintro ⟨y,hy⟩
    obtain ⟨z,hz,rfl⟩ := (componentImage_eq τ hτ x).ge hy
    exact ⟨projection θ hθ (⟨z.1,hz.1⟩,z.2),rfl⟩
  exact ⟨(Equiv.ofBijective φ ⟨hi,hs⟩).toHomeomorphOfContinuousClosed hc hc.isClosedMap,
    fun _ => rfl⟩

theorem exists_exchanged_component_homeomorph [CompactSpace S] [T2Space S]
    [LocallyConnectedSpace S] (x : S) (hx : τ x ∉ connectedComponent x) :
    ∃ W : (connectedComponent x × unitInterval) ≃ₜ
        connectedComponent (boundaryMap τ hτ x),
      ∀ z, (W z : Model τ hτ) = projection τ hτ (z.1.val,z.2) := by
  let C := connectedComponent x
  let : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  let f : C × unitInterval → connectedComponent (boundaryMap τ hτ x) := fun z =>
    ⟨projection τ hτ (z.1.val,z.2),(componentImage_eq τ hτ x).le
      ⟨(z.1.val,z.2),⟨z.1.property,mem_univ _⟩,rfl⟩⟩
  have hf : Continuous f := ((continuous_projection τ hτ).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _
  have hi : Function.Injective f := by
    intro a b hab
    rcases (projection_eq τ hτ _ _).mp (congrArg Subtype.val hab) with he | he
    · apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst he)
      · exact congrArg (fun z : S × unitInterval => z.2) he
    · have ha : τ b.1.val ∈ connectedComponent x := by
        have he1 : a.1.val = τ b.1.val := congrArg Prod.fst he
        rw [← he1]
        exact a.1.property
      have hb : τ b.1.val ∈ connectedComponent (τ x) :=
        τ.continuous.image_connectedComponent_subset x ⟨b.1.val,b.1.property,rfl⟩
      have hh := (connectedComponent_eq ha).trans (connectedComponent_eq hb).symm
      exact (hx (hh ▸ (mem_connectedComponent : τ x ∈ connectedComponent (τ x)))).elim
  have hs : Function.Surjective f := by
    rintro ⟨y,hy⟩
    obtain ⟨z,hz,rfl⟩ := (componentImage_eq τ hτ x).ge hy
    exact ⟨(⟨z.1,hz.1⟩,z.2),rfl⟩
  exact ⟨(Equiv.ofBijective f ⟨hi,hs⟩).toHomeomorphOfContinuousClosed hf hf.isClosedMap,
    fun _ => rfl⟩

end PoincareConjecture.M76.TwistedInvolutionInterval
