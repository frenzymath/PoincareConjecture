import PoincareConjecture.Proofs.M38.FullCutDiffeomorph
import PoincareConjecture.Proofs.M38.UnionRefinement
import PoincareConjecture.Proofs.M38.ComponentDecomposition
import PoincareConjecture.Proofs.M38.CappingBalls

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

theorem cappedDiscardedCarrier_nonempty_of_cap_count_pos
    (hcount : 0 < (F.event T hT).cap_count) :
    Nonempty (cappedDiscardedCarrier F T hT P).carrier :=
  ⟨(cappedCapBall F T hT P ⟨0, hcount⟩).map 0⟩

noncomputable def fullCutFamilyAssembly
    (hcount : 0 < (F.event T hT).cap_count) {m n : ℕ}
    {piecesB : Fin m → GeneralizedSliceCarrier.{u}}
    {piecesD : Fin n → GeneralizedSliceCarrier.{u}}
    (UB : SmoothDisjointUnionData piecesB (F.slice T))
    (UD : SmoothDisjointUnionData piecesD (cappedDiscardedCarrier F T hT P)) :
    SmoothFiniteConnectedSumAssembly (Fin.append piecesB piecesD)
      (partialCappedCarrier F T hT P Set.univ) where
  initial := partialCappedCarrier F T hT P Set.univ
  disjoint_union := transportUnion
    (sumRefinement UB UD inferInstance
      (cappedDiscardedCarrier_nonempty_of_cap_count_pos F T hT P hcount))
    (fullCutSumDiffeomorph F T hT P)
  operations := .refl

theorem exists_fullCutComponentAssembly
    (hcount : 0 < (F.event T hT).cap_count) :
    ∃ m : ℕ, ∃ rB : Fin m → (F.slice T).carrier,
      ∃ UB : SmoothDisjointUnionData (fun i => componentCarrier (F.slice T) (rB i))
          (F.slice T),
        (∀ i, UB.region i = connectedComponent (rB i)) ∧
        ∃ n : ℕ, ∃ rD : Fin n → (cappedDiscardedCarrier F T hT P).carrier,
          ∃ UD : SmoothDisjointUnionData
              (fun i => componentCarrier (cappedDiscardedCarrier F T hT P) (rD i))
              (cappedDiscardedCarrier F T hT P),
            (∀ i, UD.region i = connectedComponent (rD i)) ∧
            Nonempty (SmoothFiniteConnectedSumAssembly
              (Fin.append (fun i => componentCarrier (F.slice T) (rB i))
                (fun i => componentCarrier (cappedDiscardedCarrier F T hT P) (rD i)))
              (partialCappedCarrier F T hT P Set.univ)) := by
  obtain ⟨m, rB, UB, hregionB⟩ := exists_component_decomposition (F.slice T)
    (F.slices_compact T (F.surgery_times_subset hT))
  obtain ⟨n, rD, UD, hregionD⟩ := exists_component_decomposition
    (cappedDiscardedCarrier F T hT P) (cappedDiscardedCarrier_compact F T hT P)
  exact ⟨m, rB, UB, hregionB, n, rD, UD, hregionD,
    ⟨fullCutFamilyAssembly F T hT P hcount UB UD⟩⟩

end PoincareConjecture.M38
