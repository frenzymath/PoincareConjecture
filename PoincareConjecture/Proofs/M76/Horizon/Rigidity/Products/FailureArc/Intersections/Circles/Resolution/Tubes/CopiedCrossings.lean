import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.PairFibers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.RestrictedPairCoordinates



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem copied_pair_raw_crossings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    {S₀ S₁ T₀ T₁ C₀ C₁ : Set P2} {f₀ f₁ f : P2 → X}
    (a : P2 ≃ᴬ[ℝ] P2)
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁) (hT₀ : IsCompact T₀) (hT₁ : IsCompact T₁)
    (hT₀S : T₀ ⊆ S₀) (hT₁S : T₁ ⊆ S₁)
    (hf₀ : ContinuousOn f₀ S₀) (hf₁ : ContinuousOn f₁ S₁)
    (hf₀i : InjOn f₀ S₀) (hf₁i : InjOn f₁ S₁)
    (hdis : Disjoint T₀ (a '' T₁))
    (hf : ContinuousOn f (T₀ ∪ a '' T₁))
    (hkeep₀ : EqOn f f₀ T₀) (hkeep₁ : ∀ x ∈ T₁, f (a x) = f₁ x)
    (hC₀ : {x | x ∈ T₀ ∧ f₀ x ∈ f₁ '' T₁} = C₀)
    (hC₁ : {y | y ∈ T₁ ∧ f₁ y ∈ f₀ '' T₀} = C₁)
    (hC₀T : C₀ ⊆ interior T₀) (hC₁T : C₁ ⊆ interior T₁)
    (hCR : MapsTo f₀ C₀ (interior R))
    (hcharts : ∀ x ∈ C₀, Nonempty (OriginalSurfacePairChart e (f₀ '' S₀) (f₁ '' S₁) (f₀ x) false)) :
    ∀ x ∈ T₀ ∪ a '' T₁, ∀ y ∈ T₀ ∪ a '' T₁, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f (T₀ ∪ a '' T₁) R x y) := by
  have hfi₀ : InjOn f T₀ := by
    intro x hx y hy hxy
    exact hf₀i (hT₀S hx) (hT₀S hy) ((hkeep₀ hx).symm.trans (hxy.trans (hkeep₀ hy)))
  have hfi₁ : InjOn f (a '' T₁) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    exact congrArg a (hf₁i (hT₁S hx) (hT₁S hy)
      ((hkeep₁ x hx).symm.trans (hxy.trans (hkeep₁ y hy))))
  have himage₀ : f '' T₀ = f₀ '' T₀ := image_congr hkeep₀
  have himage₁ : f '' (a '' T₁) = f₁ '' T₁ := by
    rw [← image_comp]
    exact image_congr hkeep₁
  have hforward (x : P2) (hx : x ∈ T₀) (y : P2) (hy : y ∈ a '' T₁)
      (hxy : f x = f y) : Nonempty (RawSourceCrossing e f (T₀ ∪ a '' T₁) R x y) := by
    obtain ⟨v,hv,rfl⟩ := hy
    have heq : f₀ x = f₁ v := (hkeep₀ hx).symm.trans (hxy.trans (hkeep₁ v hv))
    have hxC := hC₀.subset (show x ∈ {x | x ∈ T₀ ∧ f₀ x ∈ f₁ '' T₁} from
      ⟨hx,⟨v,hv,heq.symm⟩⟩)
    have hvC := hC₁.subset (show v ∈ {y | y ∈ T₁ ∧ f₁ y ∈ f₀ '' T₀} from
      ⟨hv,⟨x,hx,heq⟩⟩)
    obtain ⟨C⟩ := hcharts x hxC
    obtain ⟨Q,hxQ,hQR,hcompat,hfirst,hsecond⟩ :=
      exists_restricted_whole_pair_coordinates hS₀ hS₁ hT₀S hT₁S hf₀ hf₁ hf₀i hf₁i
        (hC₀T hxC) (hC₁T hvC) heq (hCR hxC) C
    apply nonempty_raw_crossing_of_disjoint_source_coordinates hT₀
      (hT₁.image a.continuous) hdis hf hfi₀ hfi₁ hx ⟨v,hv,rfl⟩ hxy Q
      ((hkeep₀ hx).symm ▸ hxQ) hQR hcompat
    · simpa only [himage₀] using hfirst
    · simpa only [himage₁] using hsecond
  intro x hx y hy hne heq
  rcases opposite_source_of_equal_value hfi₀ hfi₁ hx hy hne heq with h | h
  · exact hforward x h.1 y h.2 heq
  · obtain ⟨C⟩ := hforward y h.2 x h.1 heq.symm
    exact ⟨{C with
      labels := C.labels.elim (fun hh => Or.inr ⟨hh.2,hh.1⟩) (fun hh => Or.inl ⟨hh.2,hh.1⟩)
      point := heq.symm ▸ C.point}⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
