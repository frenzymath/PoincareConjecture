import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Charts.RawPair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.PairFibers



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open CircleResolution

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem copied_proper_pair_raw_crossings
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X}
    {S₀ S₁ : Set P2} {f₀ f₁ f : P2 → X}
    (a : P2 ≃ᴬ[ℝ] P2)
    (hS₀ : IsCompact S₀) (hS₁ : IsCompact S₁)
    (hf₀i : InjOn f₀ S₀) (hf₁i : InjOn f₁ S₁)
    (hdis : Disjoint S₀ (a '' S₁))
    (hf : ContinuousOn f (S₀ ∪ a '' S₁))
    (hkeep₀ : EqOn f f₀ S₀) (hkeep₁ : ∀ x ∈ S₁, f (a x) = f₁ x)
    (hR₀ : MapsTo f₀ S₀ R)
    (hboundary : ∀ x ∈ S₀, f₀ x ∈ f₁ '' S₁ → f₀ x ∈ frontier R →
      ∃ C : OriginalSurfacePairChart e (f₀ '' S₀) (f₁ '' S₁) (f₀ x) true,
        (∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔
          0 ≤ (C.coordinates z).1.2) ∧
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔
          (C.coordinates z).1.2 = 0)
    (hinterior : ∀ x ∈ S₀, f₀ x ∈ f₁ '' S₁ → f₀ x ∈ interior R →
      Nonempty (OriginalSurfacePairChart e (f₀ '' S₀) (f₁ '' S₁) (f₀ x) false)) :
    ∀ x ∈ S₀ ∪ a '' S₁, ∀ y ∈ S₀ ∪ a '' S₁, x ≠ y → f x = f y →
      Nonempty (RawSourceCrossing e f (S₀ ∪ a '' S₁) R x y) := by
  have hfi₀ : InjOn f S₀ := by
    intro x hx y hy hxy
    exact hf₀i hx hy ((hkeep₀ hx).symm.trans (hxy.trans (hkeep₀ hy)))
  have hfi₁ : InjOn f (a '' S₁) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    exact congrArg a (hf₁i hx hy ((hkeep₁ x hx).symm.trans (hxy.trans (hkeep₁ y hy))))
  have himage₀ : f '' S₀ = f₀ '' S₀ := image_congr hkeep₀
  have himage₁ : f '' (a '' S₁) = f₁ '' S₁ := by
    rw [←image_comp]
    exact image_congr hkeep₁
  have hforward (x : P2) (hx : x ∈ S₀) (y : P2) (hy : y ∈ a '' S₁)
      (hxy : f x = f y) : Nonempty (RawSourceCrossing e f (S₀ ∪ a '' S₁) R x y) := by
    obtain ⟨v,hv,rfl⟩ := hy
    have heq : f₀ x = f₁ v := (hkeep₀ hx).symm.trans (hxy.trans (hkeep₁ v hv))
    have hx₁ : f₀ x ∈ f₁ '' S₁ := ⟨v,hv,heq.symm⟩
    by_cases hxF : f₀ x ∈ frontier R
    · obtain ⟨C,hreg,hfront⟩ := hboundary x hx hx₁ hxF
      obtain ⟨T,hxT,_,hcompat,hfirst,hsecond,hRT,hFT⟩ :=
        exists_boundary_whole_pair_coordinates C hreg hfront univ isOpen_univ (mem_univ _)
      apply nonempty_proper_raw_crossing_of_disjoint_source_coordinates hS₀
        (hS₁.image a.continuous) hdis hf hfi₀ hfi₁ hx ⟨v,hv,rfl⟩ hxy T
        ((hkeep₀ hx).symm ▸ hxT) hcompat
      · simpa only [himage₀] using hfirst
      · simpa only [himage₁] using hsecond
      · exact Or.inr ⟨hRT,hFT⟩
    · have hxR := (mem_interior_iff_notMem_frontier (hR₀ hx)).mpr hxF
      obtain ⟨C⟩ := hinterior x hx hx₁ hxR
      obtain ⟨T,hxT,hTR,hcompat,hfirst,hsecond⟩ :=
        exists_whole_pair_coordinates C (interior R) isOpen_interior hxR
      apply nonempty_raw_crossing_of_disjoint_source_coordinates hS₀
        (hS₁.image a.continuous) hdis hf hfi₀ hfi₁ hx ⟨v,hv,rfl⟩ hxy T
        ((hkeep₀ hx).symm ▸ hxT) hTR hcompat
      · simpa only [himage₀] using hfirst
      · simpa only [himage₁] using hsecond
  intro x hx y hy hne heq
  rcases opposite_source_of_equal_value hfi₀ hfi₁ hx hy hne heq with h | h
  · exact hforward x h.1 y h.2 heq
  · obtain ⟨C⟩ := hforward y h.2 x h.1 heq.symm
    exact ⟨{C with
      labels := C.labels.elim (fun hh => Or.inr ⟨hh.2,hh.1⟩) (fun hh => Or.inl ⟨hh.2,hh.1⟩)
      point := heq.symm ▸ C.point}⟩

end PoincareConjecture.M76.Dehn.Annuli
