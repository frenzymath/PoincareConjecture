import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphSectionPasting
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BarycentricOpenStars









set_option autoImplicit false
open Set StdSimplexCore

namespace PoincareConjecture.M76.CutGraph

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def faceGenerator (ends : I → Bool → V) : V ⊕ (I × Option Bool) → Finset (Coordinate V I)
  | .inl v => {Sum.inl v}
  | .inr l => {subdivisionStart ends l, subdivisionEnd l}

def abstractComplex (ends : I → Bool → V) : AbstractSimplicialComplex (Coordinate V I) where
  faces := {s | s.Nonempty ∧ ∃ j, s ⊆ faceGenerator ends j}
  isRelLowerSet_faces := by
    rintro s ⟨hs, j, hj⟩
    exact ⟨hs, fun t ht hne => ⟨hne, j, ht.trans hj⟩⟩
  singleton_mem := by
    intro j
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    cases j with
    | inl v => exact ⟨.inl v, Finset.Subset.refl _⟩
    | inr ib =>
      exact ⟨.inr (ib.1, some ib.2), by
        simp [faceGenerator, subdivisionStart, subdivisionEnd]⟩

theorem finite_abstractComplex_faces (ends : I → Bool → V) :
    (abstractComplex ends).faces.Finite := Set.toFinite _

omit [Fintype V] [Fintype I] in
theorem abstractComplex_face_card_le (ends : I → Bool → V)
    {s : Finset (Coordinate V I)} (hs : s ∈ (abstractComplex ends).faces) : s.card ≤ 2 := by
  obtain ⟨_, j, hj⟩ := hs
  apply (Finset.card_le_card hj).trans
  cases j with
  | inl v => simp [faceGenerator]
  | inr l => exact Finset.card_le_two

omit [Fintype V] [Fintype I] in
theorem faceGenerator_mem (ends : I → Bool → V) (j : V ⊕ (I × Option Bool)) :
    faceGenerator ends j ∈ (abstractComplex ends).faces := by
  refine ⟨?_, j, Finset.Subset.refl _⟩
  cases j <;> simp [faceGenerator]

omit [Fintype V] [Fintype I] in
theorem arm_face_mem (ends : I → Bool → V) (i : I) (b : Bool) :
    ({Sum.inl (ends i b), Sum.inr (i, b)} : Finset (Coordinate V I)) ∈
      (abstractComplex ends).faces := faceGenerator_mem ends (.inr (i, some b))

omit [Fintype V] [Fintype I] in
theorem bridge_face_mem (ends : I → Bool → V) (i : I) :
    ({Sum.inr (i, false), Sum.inr (i, true)} : Finset (Coordinate V I)) ∈
      (abstractComplex ends).faces := faceGenerator_mem ends (.inr (i, none))

theorem abstractComplex_barycentricSpace (ends : I → Bool → V) :
    (abstractComplex ends).toPreAbstractSimplicialComplex.barycentricSpace = carrier ends := by
  rw [← coordinateGraphCarrier_subdivision]
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨_, j, hsj⟩, hxs⟩ := mem_iUnion₂.mp hx
    have hxj : x ∈ barycentricFace (faceGenerator ends j) :=
      ⟨hxs.1, fun k hk => hxs.2 k (fun hks => hk (hsj hks))⟩
    cases j with
    | inl v =>
      have he : x = Pi.single (Sum.inl v) 1 := by
        simpa [faceGenerator, barycentricFace_eq_convexHull] using hxj
      exact Or.inl ⟨Sum.inl v, he.symm⟩
    | inr l => exact Or.inr (mem_iUnion.mpr ⟨l, hxj⟩)
  · rintro (⟨j, rfl⟩ | hx)
    · exact (abstractComplex ends).toPreAbstractSimplicialComplex.barycentricFace_subset_barycentricSpace
        ((abstractComplex ends).singleton_mem j) (single_mem_barycentricFace (by simp))
    · obtain ⟨l, hl⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨faceGenerator ends (.inr l), faceGenerator_mem ends (.inr l), hl⟩

noncomputable def realizationHomeomorph (ends : I → Bool → V) :
    carrier ends ≃ₜ (abstractComplex ends).toPreAbstractSimplicialComplex.barycentricSpace :=
  Homeomorph.setCongr (abstractComplex_barycentricSpace ends).symm

end PoincareConjecture.M76.CutGraph
