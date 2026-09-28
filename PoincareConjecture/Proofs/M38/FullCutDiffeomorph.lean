import PoincareConjecture.Proofs.M38.FullCutCover
import PoincareConjecture.Proofs.M38.FullCutSmoothSides

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

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

noncomputable def fullCutSumDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3)
      (sumCarrier (F.slice T) (cappedDiscardedCarrier F T hT P)).carrier
      (partialCappedCarrier F T hT P Set.univ).carrier ∞ :=
  (fullCutSumMap_localDiffeomorph F T hT P).diffeomorphOfBijective
    ⟨fullCutSumMap_injective F T hT P, fullCutSumMap_surjective F T hT P⟩

theorem fullCutSumDiffeomorph_apply
    (x : (sumCarrier (F.slice T) (cappedDiscardedCarrier F T hT P)).carrier) :
    fullCutSumDiffeomorph F T hT P x = fullCutSumMap F T hT P x := rfl

theorem fullCutSumDiffeomorph_post (x : (F.slice T).carrier) :
    fullCutSumDiffeomorph F T hT P (.inl x) = fullCutPostInclusion F T hT P x := rfl

theorem fullCutSumDiffeomorph_discarded (x : (cappedDiscardedCarrier F T hT P).carrier) :
    fullCutSumDiffeomorph F T hT P (.inr x) = fullCutDiscardedInclusion F T hT P x := rfl

end PoincareConjecture.M38
