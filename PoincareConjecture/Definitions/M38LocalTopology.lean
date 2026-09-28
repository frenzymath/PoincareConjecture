import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Definitions.M37SurgeryFlow









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RawNonemptyCapCorrespondence
    (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (C : SurgeryTopologyConclusion
      (F.slice (F.event T hT).tMinus) (F.slice T)) where
  cap_piece : ∀ i : Fin (F.event T hT).cap_count,
    ∃ j : Fin C.piece_count, C.kind j = .survivor ∧
      Set.Subset ((F.event T hT).caps i).carrier (C.survivor_region j)

structure RawNonemptyTopologyWitness
    (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] where
  conclusion : SurgeryTopologyConclusion
    (F.slice (F.event T hT).tMinus) (F.slice T)
  cap_correspondence : RawNonemptyCapCorrespondence F T hT conclusion

structure RawVanishingTopologyWitness
    (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times)
    [IsEmpty (F.slice T).carrier] where
  conclusion : SurgeryTopologyConclusion
    (F.slice (F.vanishing_event T hT).tMinus) (F.slice T)
  no_survivor : ∀ i, conclusion.kind i ≠ .survivor

structure RawLocalSurgeryTopologyData (F : SurgeryFlowData.{u}) where
  admissible : SurgeryFlowAdmissible F
  nonempty_reconstruction :
    ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      [Nonempty (F.slice T).carrier],
      Nonempty (RawNonemptyTopologyWitness F T hT)
  vanishing_reconstruction :
    ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      [IsEmpty (F.slice T).carrier],
      Nonempty (RawVanishingTopologyWitness F T hT)


abbrev RepairedNonemptyCapCorrespondence
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (T : ℝ) (hT : T ∈ D.flow.surgery_times)
    [Nonempty (D.flow.slice T).carrier]
    (C : SurgeryTopologyConclusion
      (D.flow.slice (D.flow.event T hT).tMinus) (D.flow.slice T)) :=
  RawNonemptyCapCorrespondence D.flow T hT C

abbrev RepairedNonemptyTopologyWitness
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (T : ℝ) (hT : T ∈ D.flow.surgery_times)
    [Nonempty (D.flow.slice T).carrier] :=
  RawNonemptyTopologyWitness D.flow T hT

abbrev RepairedVanishingTopologyWitness
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (T : ℝ) (hT : T ∈ D.flow.surgery_times)
    [IsEmpty (D.flow.slice T).carrier] :=
  RawVanishingTopologyWitness D.flow T hT

abbrev RepairedLocalSurgeryTopologyData
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀) :=
  RawLocalSurgeryTopologyData D.flow

end PoincareConjecture
