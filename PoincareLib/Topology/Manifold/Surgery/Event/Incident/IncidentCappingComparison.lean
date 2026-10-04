import PoincareLib.Topology.Manifold.Surgery.Event.Incident.IncidentCappingRegions
import PoincareLib.Topology.Manifold.Surgery.Event.Finite.FiniteCappingComparison

/-!
# Comparing a model filling with the actual capped event component

The quotient side is constructed from the event. A model-side complement
identification with the original old component and matching annular maps
then give a diffeomorphism onto the literal capped component. Classification
and existence of the model filling are not assumptions about that quotient.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (x : eventDiscardedOpen F T hT) (D : GeneralizedSliceCarrier.{u})
  (B : incidentCapIndex F T hT P x → SurgeryBallEmbedding D)
  (E : SurgeryRegionEquivalence D (componentCarrier (incidentOldCarrier F T hT) x)
    (⋃ i, (B i).closedBall)ᶜ univ)

/-- The model complement maps to the actual capped complement through
the original old inclusion. Both region maps are retained literally. -/
noncomputable def incidentCappingComplementEquivalence :
    SurgeryRegionEquivalence D
      (componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x))
      (⋃ i, (B i).closedBall)ᶜ
      (⋃ i, (incidentCapBall F T hT P x i).closedBall)ᶜ :=
  composeRegions E (incidentOldRegionEquivalence F T hT P x)

variable
  (hB : ∀ i j, i ≠ j →
    Disjoint ((B i).map '' Metric.ball 0 2) ((B j).map '' Metric.ball 0 2))
  (hmatch : ∀ i (z : capDoubleBall) (hz : 1 < ‖z.val‖),
    E.map ((B i).map z.val) = incidentAttachmentPoint F T hT P x i z hz)

include hmatch in
/-- Model-side annular matching and the actual event attachment imply
the exact annular equation required by finite capping comparison. -/
theorem incidentCappingComplementEquivalence_annulus
    (i : incidentCapIndex F T hT P x) (z : StandardCapSpace)
    (hz : z ∈ Metric.ball 0 2) (hn : 1 < ‖z‖) :
    (incidentCappingComplementEquivalence F T hT P x D B E).map ((B i).map z) =
      (incidentCapBall F T hT P x i).map z := by
  change (incidentOldRegionEquivalence F T hT P x).map
    (E.map ((B i).map z)) = _
  rw [hmatch i ⟨z, hz⟩ hn]
  exact incidentOldRegionEquivalence_attachment F T hT P x i ⟨z, hz⟩ hn

/-- Extend the given model comparison across every actual incident cap.
The codomain is the literal event component with its inherited atlas. -/
noncomputable def incidentCappingDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) D.carrier
      (componentCarrier (cappedDiscardedCarrier F T hT P)
        (cappedOldInclusion F T hT P x)).carrier ∞ :=
  finiteCappingDiffeomorph B (incidentCapBall F T hT P x)
    (incidentCappingComplementEquivalence F T hT P x D B E)
    hB (incidentCapBall_image_disjoint F T hT P x)
    (incidentCappingComplementEquivalence_annulus F T hT P x D B E hmatch)

/-- Away from the filling balls, the resulting comparison is the model
map followed by the literal old inclusion. -/
theorem incidentCappingDiffeomorph_complement {y : D.carrier}
    (hy : y ∈ (⋃ i, (B i).closedBall)ᶜ) :
    incidentCappingDiffeomorph F T hT P x D B E hB hmatch y =
      incidentOldInclusion F T hT P x (E.map y) :=
  finiteCappingDiffeomorph_complement _ _ _ _ _ _ hy

/-- Every model filling chart maps to its original quotient cap chart,
including the closed ball and the full attaching annulus. -/
theorem incidentCappingDiffeomorph_ball
    (i : incidentCapIndex F T hT P x) (z : StandardCapSpace)
    (hz : z ∈ Metric.ball 0 2) :
    incidentCappingDiffeomorph F T hT P x D B E hB hmatch ((B i).map z) =
      (incidentCapBall F T hT P x i).map z :=
  finiteCappingDiffeomorph_ball _ _ _ _ _ _ i z hz

end PoincareMT.M38
