import PoincareLib.Topology.Manifold.Surgery.Event.Full.FullCutCover
import PoincareLib.Topology.Manifold.Surgery.Event.Full.FullCutSmoothSides

/-!
# The actual smooth full-cut identification

The actual post-slice and capped discarded carrier form the full-cut
quotient with their existing smooth structures. The diffeomorphism keeps
the previously constructed sum map and hence every actual patch identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- The exact sum map is locally a diffeomorphism on its two open summands. -/
theorem fullCutSumMap_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fullCutSumMap F T hT P) := by
  intro x
  cases x with
  | inl p =>
      have hq := sumInl_localDiffeomorph (F.slice T) (cappedDiscardedCarrier F T hT P) p
      exact hq.of_comp (f := fullCutSumMap F T hT P)
        (fullCutPostInclusion_localDiffeomorph F T hT P p)
  | inr d =>
      have hq := sumInr_localDiffeomorph (F.slice T) (cappedDiscardedCarrier F T hT P) d
      exact hq.of_comp (f := fullCutSumMap F T hT P)
        (fullCutDiscardedInclusion_localDiffeomorph F T hT P d)

/-- Full capping is the actual smooth disjoint sum of the post-slice and capped discarded carrier.
Source: Morgan--Tian Proposition 15.3, pp. 357-358, using the supplied negative retained,
positive discarded and unconditional local-retention event geometry. -/
noncomputable def fullCutSumDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3)
      (sumCarrier (F.slice T) (cappedDiscardedCarrier F T hT P)).carrier
      (partialCappedCarrier F T hT P Set.univ).carrier ∞ :=
  (fullCutSumMap_localDiffeomorph F T hT P).diffeomorphOfBijective
    ⟨fullCutSumMap_injective F T hT P, fullCutSumMap_surjective F T hT P⟩

/-- The smooth identification has exactly the previously constructed forward map. -/
theorem fullCutSumDiffeomorph_apply
    (x : (sumCarrier (F.slice T) (cappedDiscardedCarrier F T hT P)).carrier) :
    fullCutSumDiffeomorph F T hT P x = fullCutSumMap F T hT P x := rfl

/-- On the actual post summand, the smooth identification keeps the same inclusion. -/
theorem fullCutSumDiffeomorph_post (x : (F.slice T).carrier) :
    fullCutSumDiffeomorph F T hT P (.inl x) = fullCutPostInclusion F T hT P x := rfl

/-- On the actual discarded summand, the smooth identification keeps the same inclusion. -/
theorem fullCutSumDiffeomorph_discarded (x : (cappedDiscardedCarrier F T hT P).carrier) :
    fullCutSumDiffeomorph F T hT P (.inr x) = fullCutDiscardedInclusion F T hT P x := rfl

end PoincareMT.M38
