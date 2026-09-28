import PoincareConjecture.Proofs.M38.FullCutComponentAssembly
import PoincareConjecture.Proofs.M38.ActualResidualAssembly
import PoincareConjecture.Proofs.M38.EventConclusion










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)




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

end PoincareConjecture.M38
