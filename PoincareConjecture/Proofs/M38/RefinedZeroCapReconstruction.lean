import PoincareConjecture.Proofs.M38.RefinedPositiveCapReconstruction
import PoincareConjecture.Proofs.M38.ZeroCapReconstruction

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem zero_cap_reconstruction_of_discarded_assembly
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
    (hcount : (F.event T hT).cap_count = 0) {n : ℕ}
    (D : Fin n → GeneralizedSliceCarrier.{u})
    (hDcompact : ∀ i, IsCompact (Set.univ : Set (D i).carrier))
    (hDconnected : ∀ i, IsConnected (Set.univ : Set (D i).carrier))
    (hDstandard : ∀ i,
      Nonempty (SurgerySphereBundle (D i)) ∨ Nonempty (SurgeryPositiveSpaceform (D i)))
    (S : SmoothFiniteConnectedSumAssembly D (cappedDiscardedCarrier F T hT P)) :
    Nonempty (RawNonemptyTopologyWitness F T hT) := by
  classical
  by_cases hD : Nonempty (cappedDiscardedCarrier F T hT P).carrier
  · exact nonempty_discarded_reconstruction_of_assembly F T hT P hD
      D hDcompact hDconnected hDstandard S
  · apply zero_cap_reconstruction F T hT hcount
    intro x hx
    exact (hD ⟨cappedOldInclusion F T hT P ⟨x, hx⟩⟩).elim

end PoincareConjecture.M38
