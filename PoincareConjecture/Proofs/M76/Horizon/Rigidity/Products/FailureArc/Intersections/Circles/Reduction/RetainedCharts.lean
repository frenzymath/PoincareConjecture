import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.LocalCharts



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_open_agreement_of_compact_replacement
    {X : Type*} [TopologicalSpace X]
    {A T T' K D D' : Set X}
    (hD : IsClosed D) (hD' : IsClosed D')
    (hT : T = K ∪ D) (hT' : T' = K ∪ D')
    (hseam : K ∩ D ⊆ D') (havoid : Disjoint D' A) :
    ∃ W : Set X, IsOpen W ∧ A ∩ T' ⊆ W ∧
      (∀ z ∈ W, z ∈ T' ↔ z ∈ T) := by
  refine ⟨(D ∪ D')ᶜ,(hD.union hD').isOpen_compl,?_,?_⟩
  · intro z hz hbad
    have hzK : z ∈ K := by
      rcases hT'.subset hz.2 with h | h
      · exact h
      · exact False.elim (disjoint_left.mp havoid h hz.1)
    rcases hbad with h | h
    · exact disjoint_left.mp havoid (hseam ⟨hzK,h⟩) hz.1
    · exact disjoint_left.mp havoid h hz.1
  · intro z hz
    rw [hT',hT]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact False.elim (hz (Or.inr h))
    · rintro (h | h)
      · exact Or.inl h
      · exact False.elim (hz (Or.inl h))

theorem OriginalSurfacePairChart.exists_after_compact_replacement
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {A T T' K D D' : Set X} {y : X} {boundary : Bool}
    (C : OriginalSurfacePairChart e A T y boundary)
    (hD : IsClosed D) (hD' : IsClosed D')
    (hT : T = K ∪ D) (hT' : T' = K ∪ D')
    (hseam : K ∩ D ⊆ D') (havoid : Disjoint D' A)
    (hy : y ∈ A ∩ T') :
    Nonempty (OriginalSurfacePairChart e A T' y boundary) := by
  obtain ⟨W,hW,hinside,hagree⟩ :=
    exists_open_agreement_of_compact_replacement hD hD' hT hT' hseam havoid
  obtain ⟨C',_⟩ := C.exists_of_local_agreement hW (hinside hy)
    (fun _ _ => Iff.rfl) hagree
  exact ⟨C'⟩

end PoincareConjecture.M76
