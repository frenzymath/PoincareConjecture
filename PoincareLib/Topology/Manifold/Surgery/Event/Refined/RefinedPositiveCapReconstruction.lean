import PoincareLib.Topology.Manifold.Surgery.Event.Full.FullCutComponentAssembly
import PoincareLib.Topology.Manifold.Surgery.Event.Actual.ActualResidualAssembly
import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventConclusion

/-!
# Actual reconstruction with refined discarded summands

A classified assembly of the capped discarded carrier may have several
pieces for one component. Lift its actual operations while preserving the
whole post carrier, then reverse the event cuts and retain the original
post components and cap correspondence in the conclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- Morgan--Tian Proposition 15.3, pp. 357-358: a finite assembly onto the
nonempty actual capped discarded carrier, with the unchanged post union,
gives a full-cut assembly whose family is exactly post followed by discarded. -/
theorem exists_fullCutRefinedAssembly_of_nonempty
    (hD : Nonempty (cappedDiscardedCarrier F T hT P).carrier) {m n : ℕ}
    {piecesB : Fin m → GeneralizedSliceCarrier.{u}}
    {piecesD : Fin n → GeneralizedSliceCarrier.{u}}
    (UB : SmoothDisjointUnionData piecesB (F.slice T))
    (S : SmoothFiniteConnectedSumAssembly piecesD (cappedDiscardedCarrier F T hT P)) :
    Nonempty (SmoothFiniteConnectedSumAssembly (Fin.append piecesB piecesD)
      (partialCappedCarrier F T hT P Set.univ)) := by
  have hI := connectedSumChain_source_nonempty S.operations hD
  let R : SmoothFiniteConnectedSumAssembly (Fin.append piecesB piecesD)
      (sumCarrier (cappedDiscardedCarrier F T hT P) (F.slice T)) := {
    initial := sumCarrier S.initial (F.slice T)
    disjoint_union := transportUnion (sumRefinement UB S.disjoint_union inferInstance hI)
      (Diffeomorph.sumComm (𝓡 3) (F.slice T).carrier ∞ S.initial.carrier)
    operations := sumConnectedSumChain S.operations (F.slice T) }
  exact exists_transportAssembly R
    ((Diffeomorph.sumComm (𝓡 3) (cappedDiscardedCarrier F T hT P).carrier ∞
      (F.slice T).carrier).trans (fullCutSumDiffeomorph F T hT P))

/-- A positive cap count supplies the actual capped-ball center required
by the refined full-cut assembly construction. -/
theorem exists_fullCutRefinedAssembly
    (hcount : 0 < (F.event T hT).cap_count) {m n : ℕ}
    {piecesB : Fin m → GeneralizedSliceCarrier.{u}}
    {piecesD : Fin n → GeneralizedSliceCarrier.{u}}
    (UB : SmoothDisjointUnionData piecesB (F.slice T))
    (S : SmoothFiniteConnectedSumAssembly piecesD (cappedDiscardedCarrier F T hT P)) :
    Nonempty (SmoothFiniteConnectedSumAssembly (Fin.append piecesB piecesD)
      (partialCappedCarrier F T hT P Set.univ)) :=
  exists_fullCutRefinedAssembly_of_nonempty F T hT P
    (cappedDiscardedCarrier_nonempty_of_cap_count_pos F T hT P hcount) UB S

/-- Morgan--Tian Proposition 15.3, pp. 357-358, with MT-NECK-SEPARATION:
a classified-piece assembly of the nonempty actual capped discarded carrier
gives the complete event witness. The actual post components,
event reversal and original cap correspondence are constructed. Producing
the classified discarded assembly remains an internal geometric obligation. -/
theorem nonempty_discarded_reconstruction_of_assembly
    (hD : Nonempty (cappedDiscardedCarrier F T hT P).carrier) {n : ℕ}
    (D : Fin n → GeneralizedSliceCarrier.{u})
    (hDcompact : ∀ i, IsCompact (Set.univ : Set (D i).carrier))
    (hDconnected : ∀ i, IsConnected (Set.univ : Set (D i).carrier))
    (hDstandard : ∀ i,
      Nonempty (SurgerySphereBundle (D i)) ∨ Nonempty (SurgeryPositiveSpaceform (D i)))
    (S : SmoothFiniteConnectedSumAssembly D (cappedDiscardedCarrier F T hT P)) :
    Nonempty (RawNonemptyTopologyWitness F T hT) := by
  obtain ⟨m, rB, UB, hregionB⟩ := exists_component_decomposition (F.slice T)
    (F.slices_compact T (F.surgery_times_subset hT))
  obtain ⟨R⟩ := exists_fullCutRefinedAssembly_of_nonempty F T hT P hD UB S
  obtain ⟨k, beta, ⟨Q⟩⟩ := exists_actualResidualAssembly F T hT P R
  exact ⟨nonemptyWitness F T hT (eventAssemblyConclusion rB UB hregionB
    (F.slices_compact T (F.surgery_times_subset hT))
    D hDcompact hDconnected hDstandard beta Q)⟩

/-- The positive-cap branch of Proposition 15.3 supplies nonemptiness
internally from the first actual cap and retains the refined discarded family. -/
theorem positive_cap_reconstruction_of_discarded_assembly
    (hcount : 0 < (F.event T hT).cap_count) {n : ℕ}
    (D : Fin n → GeneralizedSliceCarrier.{u})
    (hDcompact : ∀ i, IsCompact (Set.univ : Set (D i).carrier))
    (hDconnected : ∀ i, IsConnected (Set.univ : Set (D i).carrier))
    (hDstandard : ∀ i,
      Nonempty (SurgerySphereBundle (D i)) ∨ Nonempty (SurgeryPositiveSpaceform (D i)))
    (S : SmoothFiniteConnectedSumAssembly D (cappedDiscardedCarrier F T hT P)) :
    Nonempty (RawNonemptyTopologyWitness F T hT) :=
  nonempty_discarded_reconstruction_of_assembly F T hT P
    (cappedDiscardedCarrier_nonempty_of_cap_count_pos F T hT P hcount)
    D hDcompact hDconnected hDstandard S

end PoincareMT.M38
