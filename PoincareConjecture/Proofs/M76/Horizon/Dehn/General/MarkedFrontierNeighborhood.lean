import Mathlib.Topology.Constructions
import Mathlib.Topology.MetricSpace.Basic










set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn


theorem exists_open_frontier_mark_neighborhood
    {X : Type*} [TopologicalSpace X] {R F : Set X}
    (hF : F ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F)) :
    ∃ O : Set X, IsOpen O ∧ interior R ∪ F ⊆ O ∧ O ∩ frontier R = F := by
  obtain ⟨U, hU, hUF⟩ := isOpen_induced_iff.mp hopen
  have htrace (x : X) (hx : x ∈ frontier R) : x ∈ U ↔ x ∈ F := by
    exact Set.ext_iff.mp hUF ⟨x, hx⟩
  refine ⟨interior R ∪ U, isOpen_interior.union hU, ?_, ?_⟩
  · intro x hx
    exact hx.elim Or.inl (fun h ↦ Or.inr ((htrace x (hF h)).mpr h))
  · ext x
    constructor
    · rintro ⟨hx | hx, hfront⟩
      · exact (hfront.2 hx).elim
      · exact (htrace x hfront).mp hx
    · intro hx
      exact ⟨Or.inr ((htrace x (hF hx)).mpr hx), hF hx⟩



theorem exists_open_neighborhood_of_proper_marked_map
    {X A : Type*} [TopologicalSpace X] {R F : Set X} {S B : Set A} {f : A → X}
    (hF : F ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → X) ⁻¹' F))
    (hin : MapsTo f S R) (hproper : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ B)
    (hmark : MapsTo f B F) :
    ∃ O : Set X, IsOpen O ∧ MapsTo f S O ∧ O ∩ frontier R = F := by
  obtain ⟨O, hO, hsub, htrace⟩ := exists_open_frontier_mark_neighborhood hF hopen
  refine ⟨O, hO, ?_, htrace⟩
  intro x hx
  apply hsub
  by_cases hfront : f x ∈ frontier R
  · exact Or.inr (hmark ((hproper x hx).mp hfront))
  · apply Or.inl
    by_contra hni
    exact hfront ⟨subset_closure (hin hx), hni⟩

end PoincareConjecture.M76.Dehn
