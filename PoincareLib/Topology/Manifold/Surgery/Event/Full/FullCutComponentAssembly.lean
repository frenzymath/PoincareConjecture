import PoincareLib.Topology.Manifold.Surgery.Event.Full.FullCutDiffeomorph
import PoincareLib.Topology.Manifold.Surgery.Event.Union.UnionRefinement
import PoincareLib.Topology.Manifold.Surgery.Event.Component.ComponentDecomposition
import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingBalls

/-!
# The initial component assembly at the full actual cut

The finite post-component and capped-discarded-component families form the
literal full-cut carrier through its established smooth sum identification.
No classification or reverse connected-sum operation is needed for this
initial assembly. The positive-cap branch has an explicit capped-ball center.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- A positive actual cap count supplies a point in the literal capped
discarded quotient, namely the center of the first constructed cap ball. -/
theorem cappedDiscardedCarrier_nonempty_of_cap_count_pos
    (hcount : 0 < (F.event T hT).cap_count) :
    Nonempty (cappedDiscardedCarrier F T hT P).carrier :=
  ⟨(cappedCapBall F T hT P ⟨0, hcount⟩).map 0⟩

/-- Morgan--Tian Proposition 15.3, pp. 357-358: the exact finite unions
of the post carrier and capped discarded carrier give the initial full-cut
assembly. Both unions are transported by the literal full-cut diffeomorphism;
its operation chain is reflexive. No standard-geometry input is used. -/
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

/-- Enumerate the actual compact post and capped-discarded components and
retain their literal component regions in the initial full-cut assembly.
These same indices can be used throughout forest and residual reversal and
in the final survivor cover. Source: Proposition 15.3, pp. 357-358. -/
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

end PoincareMT.M38
