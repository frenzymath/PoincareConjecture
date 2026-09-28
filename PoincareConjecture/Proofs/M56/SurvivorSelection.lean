import PoincareConjecture.Proofs.M56.PointGroups

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture

noncomputable def m56SurvivorSelection {A B : GeneralizedSliceCarrier.{u}}
    (C : SurgeryTopologyConclusion A B) (x : B.carrier) :
    {i : Fin C.piece_count // C.kind i = .survivor ∧
      C.survivor_region i = connectedComponent x} := by
  classical
  have hex : ∃ i : Fin C.piece_count, C.kind i = .survivor ∧
      C.survivor_region i = connectedComponent x := by
    have hx : x ∈ ⋃ i : {i // C.kind i = .survivor}, C.survivor_region i.1 := by
      rw [C.survivor_cover]
      exact mem_univ _
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨z, hz⟩ := C.survivor_component i.1 i.2
    refine ⟨i.1, i.2, ?_⟩
    rw [hz] at hi ⊢
    exact connectedComponent_eq hi
  exact ⟨hex.choose, hex.choose_spec⟩

end PoincareConjecture
