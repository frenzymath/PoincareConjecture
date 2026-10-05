import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Sequences.BlowupSequence
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper

/-!
# Compact closures of actual blowup base balls

Morgan-Tian, Theorem 12.28, pp. 323-324. The lower M09 complete-Riemannian
ball theorem applies to the connected retained slices and their actual
metrics. The resulting compactness holds at every sequence index.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M35.OrdinaryRealization

/-- Theorem 12.28's retained complete slices have compact closures of their metric balls
(pp. 323-324). -/
theorem isCompact_closure_ball (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    {t : ℝ} (ht : t ∈ Ico 0 E.flow.base.lifetime)
    (p : (slice (Ico 0 E.flow.base.lifetime) t).carrier) (r : ℝ) :
    IsCompact (closure ((metric E.flow.base.flow t).ball p r)) := by
  let : ConnectedSpace (slice (Ico 0 E.flow.base.lifetime) t).carrier :=
    (sliceDiffeomorph ht).toHomeomorph.connectedSpace_iff.mpr inferInstance
  exact Proofs.M09.isCompact_closure_metric_ball (metric E.flow.base.flow t)
    ((complete_iff P E.flow.base.flow ht).mpr (E.complete t ht)) p r

/-- Theorem 11.1's compact-base-ball hypothesis holds on the same actual blowup sequence.
Used in Theorem 12.28, pp. 323-324. -/
theorem blowupSequence_balls_compact (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop) :
    BlowupBaseBallsCompact (blowupSequence P E t x ht hR) := by
  intro A _
  exact Eventually.of_forall (fun k => isCompact_closure_ball P E (ht k) _ _)

end PoincareMT.M35.OrdinaryRealization
