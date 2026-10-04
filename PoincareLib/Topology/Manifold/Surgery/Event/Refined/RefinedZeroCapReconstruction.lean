import PoincareLib.Topology.Manifold.Surgery.Event.Refined.RefinedPositiveCapReconstruction
import PoincareLib.Topology.Manifold.Surgery.Event.Zero.ZeroCapReconstruction

/-!
# Zero-cap reconstruction with refined discarded summands

Use the actual classified assembly when the discarded carrier is nonempty.
If it is empty, every pre-point is retained and the existing zero-cap
construction has no discarded component left to classify.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

/-- Morgan--Tian Proposition 15.3, pp. 357-358: a classified-piece assembly
of the literal discarded carrier gives the zero-cap event witness. An
empty discarded carrier is handled by the actual old inclusion, so this
branch does not require a discarded component or an auxiliary summand. -/
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

end PoincareMT.M38
