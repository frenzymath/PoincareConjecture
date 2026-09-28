import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.RectangleCornerContacts
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.ClosedCoverLabels

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt

theorem OriginalFaceRectangles.side_meets_cut_iff
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [DecidableEq ι]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (cut : ι → Set E) (owner : D.Arc → ι)
    (howner : ∀ a, D.arc a ⊆ cut (owner a))
    (hcontact : ∀ k i, D.carrier k ∩ cut i =
      (if owner (D.cap k false) = i then D.arc (D.cap k false) else ∅) ∪
      (if owner (D.cap k true) = i then D.arc (D.cap k true) else ∅))
    (k : D.Region) (b : Bool) (i : ι) :
    (D.side k b ∩ cut i).Nonempty ↔
      owner (D.cap k false) = i ∨ owner (D.cap k true) = i := by
  constructor
  · rintro ⟨x,hxs,hxc⟩
    have hx := (hcontact k i).subset ⟨D.side_subset_carrier k b hxs,hxc⟩
    by_cases h0 : owner (D.cap k false) = i
    · exact Or.inl h0
    by_cases h1 : owner (D.cap k true) = i
    · exact Or.inr h1
    simp [h0,h1] at hx
  · rintro (h | h)
    · obtain ⟨x,hxa,hxs⟩ := D.cap_inter_side_nonempty k false b
      exact ⟨x,hxs,h ▸ howner _ hxa⟩
    · obtain ⟨x,hxa,hxs⟩ := D.cap_inter_side_nonempty k true b
      exact ⟨x,hxs,h ▸ howner _ hxa⟩

theorem OriginalFaceRectangles.carrier_meets_cut_iff
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [DecidableEq ι]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (cut : ι → Set E) (owner : D.Arc → ι)
    (howner : ∀ a, D.arc a ⊆ cut (owner a))
    (hcontact : ∀ k i, D.carrier k ∩ cut i =
      (if owner (D.cap k false) = i then D.arc (D.cap k false) else ∅) ∪
      (if owner (D.cap k true) = i then D.arc (D.cap k true) else ∅))
    (k : D.Region) (i : ι) :
    (D.carrier k ∩ cut i).Nonempty ↔
      owner (D.cap k false) = i ∨ owner (D.cap k true) = i := by
  constructor
  · intro hne
    by_cases h0 : owner (D.cap k false) = i
    · exact Or.inl h0
    by_cases h1 : owner (D.cap k true) = i
    · exact Or.inr h1
    rw [hcontact] at hne
    simp [h0,h1] at hne
  · intro hi
    obtain ⟨x,hxs,hxc⟩ := (D.side_meets_cut_iff cut owner howner hcontact k false i).mpr hi
    exact ⟨x,D.side_subset_carrier k false hxs,hxc⟩

end PoincareConjecture.M76.PrismBelt
