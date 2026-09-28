import PoincareConjecture.Definitions.M38LocalTopology

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

theorem no_survivor_of_isEmpty
    {A B : GeneralizedSliceCarrier.{u}} [IsEmpty B.carrier]
    (C : SurgeryTopologyConclusion A B) (i : Fin C.piece_count) :
    C.kind i ≠ .survivor := by
  intro hi
  obtain ⟨x, _⟩ := C.survivor_component i hi
  exact isEmptyElim x

theorem exists_survivor_containing
    {A B : GeneralizedSliceCarrier.{u}} (C : SurgeryTopologyConclusion A B)
    {U : Set B.carrier} (hU : IsConnected U) :
    ∃ i : Fin C.piece_count, C.kind i = .survivor ∧ U ⊆ C.survivor_region i := by
  obtain ⟨x, hx⟩ := hU.nonempty
  have hxcover : x ∈ ⋃ i : {i // C.kind i = .survivor}, C.survivor_region i.1 := by
    rw [C.survivor_cover]
    exact Set.mem_univ x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxcover
  refine ⟨i.1, i.2, ?_⟩
  obtain ⟨y, hy⟩ := C.survivor_component i.1 i.2
  rw [hy] at hi ⊢
  rw [connectedComponent_eq hi]
  exact hU.subset_connectedComponent hx

def vanishingWitness
    {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
    [IsEmpty (F.slice T).carrier]
    (C : SurgeryTopologyConclusion
      (F.slice (F.vanishing_event T hT).tMinus) (F.slice T)) :
    RawVanishingTopologyWitness F T hT where
  conclusion := C
  no_survivor := no_survivor_of_isEmpty C

end PoincareConjecture.M38
